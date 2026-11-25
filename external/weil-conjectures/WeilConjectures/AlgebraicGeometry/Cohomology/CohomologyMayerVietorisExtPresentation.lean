/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.AlgebraicGeometry.Cohomology.FlatCohomologyComparison
public import Mathlib.LinearAlgebra.Prod
import WeilConjectures.AlgebraicGeometry.Cohomology.MayerVietorisGlobalExtComparison
import WeilConjectures.AlgebraicGeometry.Cohomology.MayerVietorisOpenExtComparison

/-! # Geometric Ext presentations for the Mayer--Vietoris comparison

Source: Stacks Project, Tags 01EB, 01F7 and 02KH.
(blueprint: lem-pc-cohomology-mayer-vietoris-ext-presentation)
-/

@[expose] public section

set_option autoImplicit false

universe u v w

open CategoryTheory CategoryTheory.Limits CategoryTheory.Abelian

namespace AlgebraicGeometry.Scheme.Modules

/-- A scalar-compatible presentation of three graded groups by Ext from the
three objects of a short complex. It specifies no horizontal cohomology maps.
Source: the coefficient-functor naturality in Stacks Project, Tag 01EB,
and Ext cohomology in Section 01F7.
(blueprint: lem-pc-cohomology-mayer-vietoris-ext-presentation) -/
structure H.ExtRowPresentation
    (R : Type u) [CommRing R]
    {C : Type v} [Category.{w} C] [Abelian C] [HasExt.{u} C]
    (K : ShortComplex C) (F : C) (ρ : R →+* End F)
    (A B I : ℕ → Type u)
    [∀ n, AddCommGroup (A n)] [∀ n, AddCommGroup (B n)] [∀ n, AddCommGroup (I n)]
    [∀ n, Module R (A n)] [∀ n, Module R (B n)] [∀ n, Module R (I n)] where
  eX : ∀ n, A n ≃+ Ext K.X₃ F n
  eP : ∀ n, B n ≃+ Ext K.X₂ F n
  eI : ∀ n, I n ≃+ Ext K.X₁ F n
  scalarX : ∀ n a x, eX n (a • x) = (eX n x).comp (Ext.mk₀ (ρ a).asHom) (add_zero n)
  scalarP : ∀ n a x, eP n (a • x) = (eP n x).comp (Ext.mk₀ (ρ a).asHom) (add_zero n)
  scalarI : ∀ n a x, eI n (a • x) = (eI n x).comp (Ext.mk₀ (ρ a).asHom) (add_zero n)

attribute [local instance] cohomologyHasSheafify cohomologyHasExt

private noncomputable def mappedBiprodExt
    {C : Type v} {D : Type v} [Category.{w} C] [Category.{w} D]
    [Abelian C] [Abelian D] [HasExt.{u} D]
    (G : C ⥤ D) [G.Additive] (P Q : C) (F : D) (n : ℕ) :
    Ext (G.obj (P ⊞ Q)) F n ≃+ Ext (G.obj P) F n × Ext (G.obj Q) F n where
  toFun x := ((Ext.mk₀ (G.map biprod.inl)).comp x (zero_add n),
    (Ext.mk₀ (G.map biprod.inr)).comp x (zero_add n))
  invFun x := (Ext.mk₀ (G.map biprod.fst)).comp x.1 (zero_add n) +
    (Ext.mk₀ (G.map biprod.snd)).comp x.2 (zero_add n)
  left_inv x := by
    simp only [Ext.mk₀_comp_mk₀_assoc, ← G.map_comp, ← Ext.add_comp,
      ← Ext.mk₀_add, ← G.map_add, biprod.total, G.map_id, Ext.mk₀_id_comp]
  right_inv x := by simp [Ext.comp_add, Ext.mk₀_comp_mk₀_assoc, ← G.map_comp]
  map_add' x y := by simp [Ext.comp_add]

private lemma pairScalar
    {T : Type u} [CommRing T] {C : Type v} [Category.{w} C] [Abelian C] [HasExt.{u} C]
    {P Q Z F : C} {A B : Type u} [AddCommGroup A] [AddCommGroup B]
    [Module T A] [Module T B] (ρ : T →+* End F) (n : ℕ)
    (e : A ≃+ Ext P F n) (e' : B ≃+ Ext Q F n)
    (p : Z ⟶ P) (q : Z ⟶ Q)
    (he : ∀ a x, e (a • x) = (e x).comp (Ext.mk₀ (ρ a).asHom) (add_zero n))
    (he' : ∀ a x, e' (a • x) = (e' x).comp (Ext.mk₀ (ρ a).asHom) (add_zero n))
    (a : T) (x : A × B) :
    (Ext.mk₀ p).comp (e (a • x.1)) (zero_add n) +
      (Ext.mk₀ q).comp (e' (a • x.2)) (zero_add n) =
    ((Ext.mk₀ p).comp (e x.1) (zero_add n) +
      (Ext.mk₀ q).comp (e' x.2) (zero_add n)).comp (Ext.mk₀ (ρ a).asHom) (add_zero n) := by
  rw [he, he', Ext.add_comp]
  exact congrArg₂ (· + ·)
    (Ext.comp_assoc_of_third_deg_zero (Ext.mk₀ p) (e x.1) (Ext.mk₀ (ρ a).asHom)
      (zero_add n)).symm
    (Ext.comp_assoc_of_third_deg_zero (Ext.mk₀ q) (e' x.2) (Ext.mk₀ (ρ a).asHom)
      (zero_add n)).symm

private lemma pairComparison
    {C D : Type v} [Category.{w} C] [Category.{w} D] [Abelian C] [Abelian D]
    [HasExt.{u} C] [HasExt.{u} D] (G : C ⥤ D) [G.Additive]
    [PreservesFiniteLimits G] [PreservesFiniteColimits G]
    {P Q Z F : C} {N : D} (φ : G.obj F ⟶ N) (n : ℕ)
    (p : Z ⟶ P) (q : Z ⟶ Q) (x : Ext P F n) (y : Ext Q F n) :
    (Ext.mk₀ (G.map p)).comp
        ((x.mapExactFunctor G).comp (Ext.mk₀ φ) (add_zero n)) (zero_add n) +
      (Ext.mk₀ (G.map q)).comp
        ((y.mapExactFunctor G).comp (Ext.mk₀ φ) (add_zero n)) (zero_add n) =
    (((Ext.mk₀ p).comp x (zero_add n) +
      (Ext.mk₀ q).comp y (zero_add n)).mapExactFunctor G).comp (Ext.mk₀ φ) (add_zero n) := by
  rw [Ext.mapExactFunctor_add, Ext.add_comp, Ext.mapExactFunctor_comp,
    Ext.mapExactFunctor_comp, Ext.mapExactFunctor_mk₀, Ext.mapExactFunctor_mk₀]
  exact congrArg₂ (· + ·)
    (Ext.comp_assoc_of_third_deg_zero (Ext.mk₀ (G.map p)) (x.mapExactFunctor G)
      (Ext.mk₀ φ) (zero_add n)).symm
    (Ext.comp_assoc_of_third_deg_zero (Ext.mk₀ (G.map q)) (y.mapExactFunctor G)
      (Ext.mk₀ φ) (zero_add n)).symm

variable {R S : Type u} [CommRing R] [CommRing S] [Algebra R S]
    {X : Scheme.{u}}

/-- The geometric realization of the two cohomology rows as contravariant Ext
from one short exact sequence and its exact inverse image. The vertical identities
identify the actual comparison maps with exact-functor action on Ext followed by
the coefficient morphism. No row maps, row exactness, or connecting squares are
asserted here.

Source: Stacks Project, Tag 01EB (the free-sheaf Mayer--Vietoris sequence),
Section 01F7 (pullback of cohomology), and Tag 02KH (the two-open argument).
(blueprint: lem-pc-cohomology-mayer-vietoris-ext-presentation)

Proof: Let F be the underlying abelian sheaf of M. For an open W of X, the
free abelian sheaf represented by W represents sections on W. The adjunction for
restriction and extension by zero, which are exact for an open immersion, gives
Ext from this free sheaf to F as the Ext cohomology of the restriction of M to W.
These identifications are additive and natural in F. The free sheaves on U, V,
U intersect V and X form the short exact sequence with injection (inclusion,
minus inclusion) and surjection the sum of inclusions; stalkwise, this is the
usual exact sequence of free abelian groups for a two-open cover. Choose it as K.
The direct-sum Ext identification gives the product term. Scalar multiplication
on cohomology is postcomposition with multiplication on F; naturality of the
adjunction identifications gives all three upper scalar equations.

Apply exact inverse image G along the cartesian projection X_S to X to K.
Inverse image of the free sheaf represented by W is the free sheaf represented
by its preimage: their Hom functors both give sections of pushforward on W,
by the inverse-image adjunction and the free-sheaf universal property. The
isomorphisms commute with inclusions, and G preserves finite direct sums.
Identify each base-changed open scheme with its preimage in X_S by its
cartesian open-subscheme isomorphism. Composition of module pullback identifies
the coefficient sheaves. This gives the lower Ext presentations, with the same
signs. Their naturality in the coefficient sheaf gives the lower scalar equations.

Under these identifications, the constant-sheaf comparison on X and the
free-sheaf comparison on W agree with the inverse-image adjunction. Consequently
pullback on each Ext group is exact-functor action followed by postcomposition
with the coefficient map adjoint to the module pullback unit. This is precisely
H.baseChangeLinear, as defined in FlatCohomologyComparison, giving the three
vertical identities. For the product term, use additivity and the natural
Ext direct-sum decomposition. This argument works for empty opens, repeated
opens and the zero ring, and requires no flatness or quasi-coherence. -/
theorem H.exists_mayerVietoris_extPresentation
    (f : X ⟶ Spec (.of R)) (M : X.Modules)
    (U V : X.Opens) (hcover : U ⊔ V = ⊤) :
    let F := (SheafOfModules.toSheaf X.ringCatSheaf).obj M
    let G := invImage (baseChangeFst (S := S) f)
    let N := (SheafOfModules.toSheaf (baseChangedScheme (S := S) f).ringCatSheaf).obj
      (baseChangedModule (S := S) f M)
    let φ := coeff (baseChangeFst (S := S) f) (baseChangeUnit (S := S) f M)
    let ρ := (scalarRep M).comp (((Scheme.ΓSpecIso (.of R)).inv ≫ f.appTop).hom)
    let τ := (scalarRep (baseChangedModule (S := S) f M)).comp
      (((Scheme.ΓSpecIso (.of S)).inv ≫ (baseChangeSnd (S := S) f).appTop).hom)
    let A := fun (W : X.Opens) (n : ℕ) ↦
      HOver (W.ι ≫ f) ((pullback W.ι).obj M) n
    let B := fun (W : X.Opens) (n : ℕ) ↦
      HOver (baseChangeSnd (S := S) (W.ι ≫ f))
        (baseChangedModule (S := S) (W.ι ≫ f) ((pullback W.ι).obj M)) n
    let AX := fun n : ℕ ↦ HOver f M n
    let BX := fun n : ℕ ↦
      HOver (baseChangeSnd (S := S) f) (baseChangedModule (S := S) f M) n
    ∃ (K : ShortComplex (Sheaf (Opens.grothendieckTopology X) AddCommGrpCat.{u}))
      (_hK : K.ShortExact)
      (E : H.ExtRowPresentation R K F ρ AX
        (fun n ↦ A U n × A V n) (fun n ↦ A (U ⊓ V) n))
      (E' : H.ExtRowPresentation S (K.map G) N τ BX
        (fun n ↦ B U n × B V n) (fun n ↦ B (U ⊓ V) n)),
      (∀ n x, E'.eX n (H.baseChangeLinear (S := S) f M n x) =
        ((E.eX n x).mapExactFunctor G).comp (Ext.mk₀ φ) (add_zero n)) ∧
      (∀ n (x : A U n × A V n), E'.eP n
        (H.baseChangeLinear (S := S) (U.ι ≫ f) ((pullback U.ι).obj M) n x.1,
         H.baseChangeLinear (S := S) (V.ι ≫ f) ((pullback V.ι).obj M) n x.2) =
        ((E.eP n x).mapExactFunctor G).comp (Ext.mk₀ φ) (add_zero n)) ∧
      (∀ n x, E'.eI n
        (H.baseChangeLinear (S := S) ((U ⊓ V).ι ≫ f) ((pullback (U ⊓ V).ι).obj M) n x) =
        ((E.eI n x).mapExactFunctor G).comp (Ext.mk₀ φ) (add_zero n)) := by
  classical
  dsimp only
  obtain ⟨eX, eX', hsX, hsX', hbX⟩ := H.globalFreeExtComparison (S := S) f M
  obtain ⟨eU, eU', hsU, hsU', hbU⟩ := H.openFreeExtComparison (S := S) f M U
  obtain ⟨eV, eV', hsV, hsV', hbV⟩ := H.openFreeExtComparison (S := S) f M V
  obtain ⟨eI, eI', hsI, hsI', hbI⟩ := H.openFreeExtComparison (S := S) f M (U ⊓ V)
  let K := H.openFreeShortComplex U V
  let G := invImage (baseChangeFst (S := S) f)
  let N := (SheafOfModules.toSheaf (baseChangedScheme (S := S) f).ringCatSheaf).obj
    (baseChangedModule (S := S) f M)
  let ρ := (scalarRep M).comp (((Scheme.ΓSpecIso (.of R)).inv ≫ f.appTop).hom)
  let τ := (scalarRep (baseChangedModule (S := S) f M)).comp
    (((Scheme.ΓSpecIso (.of S)).inv ≫ (baseChangeSnd (S := S) f).appTop).hom)
  let eP := fun n ↦ ((eU n).prodCongr (eV n)).trans Ext.biprodAddEquiv.symm
  let eP' := fun n ↦ ((eU' n).prodCongr (eV' n)).trans
    (mappedBiprodExt G (H.openFreeSheaf U) (H.openFreeSheaf V) N n).symm
  let E : H.ExtRowPresentation R K _ ρ _ _ _ :=
    ⟨eX, eP, eI, hsX, (fun n a x ↦
      pairScalar ρ n (eU n) (eV n) biprod.fst biprod.snd (hsU n) (hsV n) a x), hsI⟩
  let E' : H.ExtRowPresentation S (K.map G) N τ _ _ _ :=
    ⟨eX', eP', eI', hsX', (fun n a x ↦
      pairScalar τ n (eU' n) (eV' n) (G.map biprod.fst) (G.map biprod.snd)
        (hsU' n) (hsV' n) a x), hsI'⟩
  refine ⟨K, H.openFreeShortComplex_shortExact U V hcover, E, E', hbX, ?_, hbI⟩
  intro n x
  have hu := hbU n x.1
  have hv := hbV n x.2
  exact (congrArg₂ (fun a b ↦ (Ext.mk₀ (G.map biprod.fst)).comp a (zero_add n) +
    (Ext.mk₀ (G.map biprod.snd)).comp b (zero_add n)) hu hv).trans
    (pairComparison G _ n biprod.fst biprod.snd (eU n x.1) (eV n x.2))


end AlgebraicGeometry.Scheme.Modules
