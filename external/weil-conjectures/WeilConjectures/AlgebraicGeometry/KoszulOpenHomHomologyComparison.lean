/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.AlgebraicGeometry.KoszulCechComparisonConstruction
import WeilConjectures.AlgebraicGeometry.AffineKProjectiveHomComplex
import WeilConjectures.AlgebraicGeometry.KoszulChainRestrictionFormula
import Mathlib.LinearAlgebra.ExteriorPower.Basis
import Mathlib.Algebra.Category.ModuleCat.Projective

/-! # The stagewise derived Hom identification for the Koszul comparison

Source: Stacks Project, Tags 06Z0, 08DC and 08DD.
(blueprint: lem-sc-koszul-open-hom-homology-comparison).
-/

@[expose] public section

universe u w v
open CategoryTheory CategoryTheory.Limits
namespace AlgebraicGeometry
attribute [local instance] Functor.additive_of_preserves_binary_products
  comp_preservesFiniteLimits comp_preservesFiniteColimits

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
/-- Derived Hom from each Koszul tail is its Hom-complex cohomology, naturally in
power transitions. The canonical comparison sends a restriction-zero arrow to zero.
This statement does not assert exactness of a filtered colimit, injectivity of the
comparison on cohomology, or eventual vanishing.
Source: Stacks Project, Tag 06Z0 and Equation 36.9.4.1, Tag 08DC; Tag 08DD.
(blueprint: lem-sc-koszul-open-hom-homology-comparison)

Proof: On the affine scheme, termwise quasi-coherence identifies F with the tilde
of its global-sections complex M, naturally in the differentials. The affine
quasi-coherent derived equivalence identifies derived sheaf arrows from I_e into
Q(F) with derived module arrows from the extended module tail into M. The tail
has finite free terms and is bounded, so it is K-projective. Localization thus
identifies these arrows with homotopy classes of chain maps. The degree-zero
cycles of the linear Hom complex are exactly chain maps, and its boundaries are
null-homotopic maps. Take the inverse of this additive identification, and compose
with postcomposition by the inverse of the specified isomorphism to E. The object
identification koszulCechHomObjIso gives the displayed additive equivalences.
Precomposition of Hom cochains agrees with composition of chain maps; the power
transition formula for koszulCechHomDiagram therefore proves their naturality.
For the last clause, represent an arrow by such a module chain map. On the
principal intersection indexed by J, the Koszul-to-Cech comparison evaluates
that map on the ordered exterior generator and divides by the product of the
f_j to the stage exponent, with its specified totalization sign. This is exactly
the chain-level restriction followed by the inverse of the restricted augmentation:
the restricted Koszul complex contracts when one f_j is invertible. The Cech to
RΓ map and evaluation-at-one identification of Hom(O_U,E|_U) with H^0(RΓ(U,E))
identify its class with the given composite on derived homology. Restriction-zero
arrows therefore give the zero class. The argument uses no exactness of colimits
or invertibility of the comparison. For the empty cover, all tails and comparison
sources vanish; the zero ring and F=0 give zero groups by the same constructions. -/
theorem koszulOpenHom_homology_comparison
    (A : Type u) [CommRing A] (r : ℕ) (f : Fin r → A)
    [HasDerivedCategory.{w}
      (SheafOfModules.{u} (moduleRings (Spec (.of A)).toRingedSpace))]
    [∀ V : (Spec (.of A)).Opens, HasDerivedCategory.{w}
      (SheafOfModules.{u} ((moduleRings (Spec (.of A)).toRingedSpace).over V))]
    [HasDerivedCategory.{w}
      (SheafOfModules.{u} (moduleRings (koszulOpen A r f).toScheme.toRingedSpace))]
    [HasDerivedCategory.{v} (ModuleCat.{u} A)]
    (F : CochainComplex
      (SheafOfModules.{u} (moduleRings (Spec (.of A)).toRingedSpace)) ℤ)
    (hF : ∀ n : ℤ, (F.X n).IsQuasicoherent)
    (E : schemeDerivedQCohCategory (Spec (.of A)))
    (eF : DerivedCategory.Q.obj F ≅ E.obj) :
    let R := ((SheafOfModules.overFunctor.{u}
      (moduleRings (Spec (.of A)).toRingedSpace) (koszulOpen A r f)) ⋙
      Equivalence.functor
        (C := SheafOfModules.{u}
          ((moduleRings (Spec (.of A)).toRingedSpace).over (koszulOpen A r f)))
        (D := SheafOfModules.{u}
          (moduleRings (koszulOpen A r f).toScheme.toRingedSpace))
        (Scheme.Modules.overEquiv (koszulOpen A r f))).mapDerivedCategory
    let M := ((affineOpenSections A ⊤).mapHomologicalComplex (.up ℤ)).obj F
    let D := koszulCechHomDiagram A r f M
    let C := koszulCechHomColimit A r f M
    let β := ((DerivedCategory.homologyFunctorFactors (ModuleCat.{u} A) 0).app C).inv ≫
      (DerivedCategory.homologyFunctor (ModuleCat.{u} A) 0).map
        (koszulCechDerivedComparison A r f F ≫
          (affineOpenSections A (koszulOpen A r f)).rightDerivedFunctor.map eF.hom)
    ∃ α : ∀ e : ℕ, (koszulOpenObject A r f e ⟶ E.obj) ≃+ (D.obj e).homology 0,
      (∀ (a b : ℕ) (h : a ≤ b) (φ : koszulOpenObject A r f a ⟶ E.obj),
        α b (koszulOpenMap A r f a b h ≫ φ) =
          HomologicalComplex.homologyMap (D.map (homOfLE h)) 0 (α a φ)) ∧
      ∀ (e : ℕ) (φ : koszulOpenObject A r f e ⟶ E.obj), R.map φ = 0 →
        β (HomologicalComplex.homologyMap (colimit.ι D e) 0 (α e φ)) = 0 := by
  classical
  dsimp only
  let M := ((affineOpenSections A ⊤).mapHomologicalComplex (.up ℤ)).obj F
  let T := (koszulOpenTilde A).mapHomologicalComplex (.up ℤ)
  let L (e : ℕ) := (koszulOpenTail A r f e).extend ComplexShape.embeddingDownNat
  let D := koszulCechHomDiagram A r f M
  let j (e : ℕ) := koszulCechHomObjIso A r f M e
  let s : T.obj M ≅ F := HomologicalComplex.Hom.isoOfComponents
    (fun n ↦ by
      have : (F.X n).IsQuasicoherent := hF n
      have : IsIso (Scheme.Modules.fromTildeΓ (R := .of A) (F.X n)) :=
        Scheme.Modules.isIso_fromTildeΓ_of_isQuasicoherent (R := .of A) (F.X n)
      exact asIso (Scheme.Modules.fromTildeΓ (R := .of A) (F.X n)))
    (fun n m _ ↦ by
      change Scheme.Modules.fromTildeΓ (R := .of A) (F.X n) ≫ F.d n m = _
      exact ((Scheme.Modules.fromTildeΓNatTrans (R := .of A)).naturality (F.d n m)).symm)
  let q := DerivedCategory.Q.mapIso s ≪≫ eF
  have hL (e : ℕ) : CochainComplex.IsKProjective (L e) := by
    let : ∀ n, Projective ((koszulOpenTail A r f e).X n) := fun n ↦ by
      change Projective (ModuleCat.of A (⋀[A]^(n + 1) (Fin r →₀ A)))
      exact ModuleCat.projective_of_free (Module.Free.chooseBasis A _)
    infer_instance
  obtain ⟨a, ha, hrep⟩ := affineKProjective_homComplex A M
  let p (e : ℕ) : (koszulOpenObject A r f e ⟶ E.obj) ≃+
      (DerivedCategory.Q.obj (T.obj (L e)) ⟶ DerivedCategory.Q.obj (T.obj M)) :=
    { toFun := fun φ ↦ φ ≫ q.inv
      invFun := fun φ ↦ φ ≫ q.hom
      left_inv := fun φ ↦ by simp
      right_inv := fun φ ↦ by simp
      map_add' := fun φ ψ ↦ by simp only [Preadditive.add_comp] }
  let k (e : ℕ) : (CochainComplex.moduleHomComplex (L e) M).homology 0 ≃+
      (D.obj e).homology 0 := ((HomologicalComplex.homologyFunctor
    (ModuleCat.{u} A) (.up ℤ) 0).mapIso (j e).symm).toLinearEquiv.toAddEquiv
  let α (e : ℕ) : (koszulOpenObject A r f e ⟶ E.obj) ≃+ (D.obj e).homology 0 :=
    (p e).trans ((a (L e) (hL e)).trans (k e))
  refine ⟨α, ?_, ?_⟩
  · intro x y h φ
    let g := HomologicalComplex.extendMap (koszulOpenTransition A r f x y h)
      ComplexShape.embeddingDownNat
    let t := (j x).inv ≫ D.map (homOfLE h) ≫ (j y).hom
    have ht (n : ℤ) (z : CochainComplex.HomComplex.Cochain (L x) M n) :
        (t.f n) z = (CochainComplex.HomComplex.Cochain.ofHom g).comp z (zero_add n) := by
      exact (koszulCechHomDiagram_exists A r f M).choose_spec.2 x y h n z
        ((koszulCechHomDiagram_exists A r f M).choose_spec.1 x)
        ((koszulCechHomDiagram_exists A r f M).choose_spec.1 y)
    have hh := ha (L x) (L y) (hL x) (hL y) g t ht (p x φ)
    have hp : p y (koszulOpenMap A r f x y h ≫ φ) =
        DerivedCategory.Q.map (T.map g) ≫ p x φ := by
      exact Category.assoc _ _ _
    calc
      α y (koszulOpenMap A r f x y h ≫ φ) =
          (k y) (a (L y) (hL y) (DerivedCategory.Q.map (T.map g) ≫ p x φ)) :=
        congrArg ((a (L y) (hL y)).trans (k y)) hp
      _ = (k y) (HomologicalComplex.homologyMap t 0 (a (L x) (hL x) (p x φ))) :=
        congrArg (k y) hh
      _ = HomologicalComplex.homologyMap (D.map (homOfLE h)) 0 (α x φ) := by
        change (HomologicalComplex.homologyMap t 0 ≫
          HomologicalComplex.homologyMap (j y).inv 0) _ =
            (HomologicalComplex.homologyMap (j x).inv 0 ≫
              HomologicalComplex.homologyMap (D.map (homOfLE h)) 0) _
        congr 1
        rw [← HomologicalComplex.homologyMap_comp, ← HomologicalComplex.homologyMap_comp]
        simp [t]
  · intro e φ hφ
    obtain ⟨g, z, hg, hz, hclass⟩ := hrep (L e) (hL e) (p e φ)
    have hφrep : DerivedCategory.Q.map (T.map g) ≫ q.hom = φ := by
      rw [hg]
      change (φ ≫ q.inv) ≫ q.hom = φ
      simp
    obtain ⟨b, hb⟩ := koszulChain_restriction_formula A r f F hF E eF s (fun _ ↦ by simp [s])
    have hφrep' : DerivedCategory.Q.map (T.map g) ≫
        DerivedCategory.Q.map s.hom ≫ eF.hom = φ := hφrep
    have hzero := hb e g z hz 0 (by
      rw [comp_zero]
      exact ((congrArg _ hφrep').trans hφ).symm)
    rw [map_zero] at hzero
    have hα : α e φ = HomologicalComplex.homologyMap (j e).inv 0
        ((CochainComplex.moduleHomComplex (L e) M).homologyπ 0 z) := by
      change (k e) (a (L e) (hL e) (p e φ)) = _
      rw [hclass]
      rfl
    exact (congrArg (fun x : (D.obj e).homology 0 ↦
      (((DerivedCategory.homologyFunctorFactors (ModuleCat.{u} A) 0).app
        (koszulCechHomColimit A r f M)).inv ≫
        (DerivedCategory.homologyFunctor (ModuleCat.{u} A) 0).map
          (koszulCechDerivedComparison A r f F ≫
            (affineOpenSections A (koszulOpen A r f)).rightDerivedFunctor.map eF.hom))
              (HomologicalComplex.homologyMap (colimit.ι D e) 0 x)) hα).trans hzero.symm

end AlgebraicGeometry
