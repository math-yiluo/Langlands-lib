/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import Mathlib.Algebra.Category.Grp.AB
public import Mathlib.Algebra.Category.ModuleCat.Projective
public import Mathlib.AlgebraicGeometry.Sites.EtalePoint
public import Mathlib.CategoryTheory.Abelian.GrothendieckCategory.HasExt
public import Mathlib.CategoryTheory.Sites.EpiMono
public import WeilConjectures.AlgebraicGeometry.Sites.Hilbert90
public import WeilConjectures.AlgebraicGeometry.Sites.PointFunctions
public import WeilConjectures.CategoryTheory.GrothendieckAbelian.ConcreteCoefficients
public import WeilConjectures.CategoryTheory.GrothendieckAbelian.Sheaf
public import WeilConjectures.Mathlib.Algebra.Category.Grp.ForgetCorepresentable
public import WeilConjectures.Mathlib.CategoryTheory.Sites.SheafCohomology.Basic
public import Mathlib.Algebra.Homology.DerivedCategory.Ext.EnoughProjectives

/-!
# Étale cohomology of the constant sheaf `ℤ` on the spectrum of a field

The étale cohomology of the spectrum of a field `K` is the Galois cohomology of
`Gal(Kˢᵉᵖ/K)`. For the constant sheaf `ℤ` this gives:

- in degree `1`, `H¹(Spec K_ét, ℤ) = Hom_cont(Gal(Kˢᵉᵖ/K), ℤ) = 0`, since a continuous
  homomorphism from a profinite group to the discrete torsion-free group `ℤ` has finite, hence
  trivial, image;
- in every positive degree, `Hⁿ(Spec k_ét, ℤ) = 0` for `k` separably closed, since then the
  Galois group is trivial.

Along the way we record that for `k` separably closed an étale sheaf on `Spec k` is determined
by its global sections, since every étale `k`-scheme is covered by its `k`-points.

## Main statements

- `AlgebraicGeometry.Scheme.surjective_app_of_epi_of_isSepClosed`: for `k` separably closed,
  an epimorphism of étale sheaves on `Spec k` (with values in a concrete category such as
  abelian groups or modules) is surjective on global sections.
- `AlgebraicGeometry.Scheme.eq_of_forall_restrict_eq_of_isSepClosed`: two sections of an étale
  sheaf on `Spec k` agreeing at every `k`-point are equal.
- `AlgebraicGeometry.Scheme.isZero_of_subsingleton_sections_of_isSepClosed`: an étale sheaf of
  modules on `Spec k` without nonzero global sections is zero.
- `AlgebraicGeometry.Scheme.subsingleton_H_constantSheaf_of_isSepClosed`:
  `H^q(Spec k_ét, ℤ) = 0` for `q ≥ 1` and `k` separably closed.
- `AlgebraicGeometry.Scheme.surjective_app_of_shortExact_constantSheaf_int`: every `ℤ`-torsor
  on `Spec K` is trivial, in the form: for `0 → ℤ → E → Q → 0` exact, `Γ(E) → Γ(Q)` is
  surjective.
- `AlgebraicGeometry.Scheme.subsingleton_H_one_constantSheaf_of_field` and
  `AlgebraicGeometry.Scheme.subsingleton_H_one_constantSheaf_of_isField`:
  `H¹(Spec K_ét, ℤ) = 0` for every field `K`.

## Implementation details

We do not go through Galois cohomology. For `k` separably closed, every étale covering of
`Spec k` has a section, so the global sections functor is exact and the constant sheaf `ℤ`,
which corepresents it, is a projective sheaf. In degree `1` and for an arbitrary field `K`, a
`ℤ`-torsor is trivialised over `Spec L` for a finite separable extension `L` of `K`, and the
descent datum is a function on the finite set of points of `Spec (L ⊗_K L)` whose set of values
is closed under addition, hence zero.
-/

@[expose] public section

universe u

open CategoryTheory Opposite

namespace AlgebraicGeometry.Scheme

section EtalePoint

variable (k : Type u) [Field k]

/-- The terminal object `𝟙 : Spec k ⟶ Spec k` of the small étale site of `Spec k`, as an object
of `(Spec k).Etale`. -/
noncomputable def etalePoint : (Spec (.of k)).Etale :=
  MorphismProperty.Over.mk ⊤ (𝟙 (Spec (CommRingCat.of k)))
    (MorphismProperty.id_mem @AlgebraicGeometry.Etale (Spec (CommRingCat.of k)))

variable {k} in
/-- `𝟙 : Spec k ⟶ Spec k` is the terminal object of the small étale site of `Spec k`. -/
noncomputable def isTerminalEtalePoint : Limits.IsTerminal (etalePoint k) :=
  MorphismProperty.Over.mkIdTerminal @AlgebraicGeometry.Etale (Spec (.of k))

end EtalePoint

section IsSepClosed

variable (k : Type u) [Field k] [IsSepClosed k]

/-- Let `X` be a scheme isomorphic to `Spec k` for a separably closed field `k`. Every covering
sieve of the terminal object `X` of the small étale site of `X` contains the identity. -/
lemma id_mem_of_mem_smallEtaleTopology_of_iso {k} [Field k] [IsSepClosed k] {X : Scheme.{u}}
    (e : X ≅ Spec (.of k)) {R : Sieve (Etale.mk (𝟙 X))} (hR : R ∈ X.smallEtaleTopology _) :
    R.arrows (𝟙 _) := by
  obtain ⟨𝒰, h𝒰, p, hle⟩ := (mem_smallGrothendieckTopology _ _).1 hR
  obtain ⟨j, y, hy⟩ := 𝒰.exists_eq (e.inv (default : Spec (.of k)))
  obtain ⟨l, hl, -⟩ := exists_fac_of_etale_of_isSepClosed (𝒰.f j) e.inv y (by rw [hy]; rfl)
  have hl' : (e.hom ≫ l) ≫ 𝒰.f j = 𝟙 X := by rw [Category.assoc, hl, e.hom_inv_id]
  have hmem : R.arrows ((𝒰.f j).asOverProp _) := hle _ _ (Presieve.ofArrows.mk j)
  convert R.downward_closed hmem (MorphismProperty.Over.homMk (A := Etale.mk (𝟙 X))
    (B := (𝒰.X j).asOverProp _ (p j)) (e.hom ≫ l) (by
      change (e.hom ≫ l) ≫ (𝒰.X j ↘ _) = 𝟙 _
      rw [← comp_over (𝒰.f j), ← Category.assoc, hl', Category.id_comp]
      rfl))
  exact MorphismProperty.Over.Hom.ext hl'.symm

/-- Over a separably closed field `k`, every covering sieve of `Spec k` in the small étale site
contains the identity. -/
lemma id_mem_of_mem_smallEtaleTopology_of_isSepClosed (R : Sieve (etalePoint k))
    (hR : R ∈ (Spec (.of k)).smallEtaleTopology (etalePoint k)) : R.arrows (𝟙 _) :=
  id_mem_of_mem_smallEtaleTopology_of_iso (Iso.refl _) hR

section Concrete

variable {A : Type*} [Category A] {FA : A → A → Type*} {CA : A → Type*}
  [∀ X Y, FunLike (FA X Y) (CA X) (CA Y)] [ConcreteCategory A FA]
  [ConcreteCategory.HasFunctorialSurjectiveInjectiveFactorization A]

/-- Let `X` be a scheme isomorphic to `Spec k` for a separably closed field `k`. An epimorphism
of étale sheaves on `X` with values in a concrete category `A` (for instance abelian groups or
modules) is surjective on sections over `X`. -/
lemma surjective_app_of_epi_of_iso {k} [Field k] [IsSepClosed k] {X : Scheme.{u}}
    (e : X ≅ Spec (.of k))
    [X.smallEtaleTopology.WEqualsLocallyBijective A] [HasSheafify X.smallEtaleTopology A]
    [X.smallEtaleTopology.HasSheafCompose (CategoryTheory.forget A)]
    [Balanced (Sheaf X.smallEtaleTopology A)]
    {F G : Sheaf X.smallEtaleTopology A} (φ : F ⟶ G) [Epi φ] :
    Function.Surjective (φ.hom.app (op (Etale.mk (𝟙 X)))) := by
  have := (Sheaf.isLocallySurjective_iff_epi' A φ).2 inferInstance
  intro s
  obtain ⟨t, ht⟩ := id_mem_of_mem_smallEtaleTopology_of_iso e
    (Presheaf.imageSieve_mem X.smallEtaleTopology φ.hom (U := op (Etale.mk (𝟙 X))) s)
  exact ⟨t, ht.trans (by simp)⟩

/-- Over a separably closed field `k`, an epimorphism of étale sheaves on `Spec k` with values
in a concrete category `A` (for instance abelian groups or modules) is surjective on global
sections. -/
lemma surjective_app_of_epi_of_isSepClosed
    [(Spec (.of k)).smallEtaleTopology.WEqualsLocallyBijective A]
    [HasSheafify (Spec (.of k)).smallEtaleTopology A]
    [(Spec (.of k)).smallEtaleTopology.HasSheafCompose (CategoryTheory.forget A)]
    [Balanced (Sheaf (Spec (.of k)).smallEtaleTopology A)]
    {F G : Sheaf (Spec (.of k)).smallEtaleTopology A} (φ : F ⟶ G) [Epi φ] :
    Function.Surjective (φ.hom.app (op (etalePoint k))) :=
  surjective_app_of_epi_of_iso (Iso.refl _) φ

/-- Let `X` be a scheme isomorphic to `Spec k` for a separably closed field `k`. Taking sections
over `X` preserves epimorphisms of étale sheaves on `X` with values in a concrete category. -/
lemma preservesEpimorphisms_sheafSections_of_iso {k} [Field k] [IsSepClosed k]
    {X : Scheme.{u}} (e : X ≅ Spec (.of k))
    [X.smallEtaleTopology.WEqualsLocallyBijective A] [HasSheafify X.smallEtaleTopology A]
    [X.smallEtaleTopology.HasSheafCompose (CategoryTheory.forget A)]
    [Balanced (Sheaf X.smallEtaleTopology A)] :
    ((sheafSections X.smallEtaleTopology A).obj (op (Etale.mk (𝟙 X)))).PreservesEpimorphisms
    where
  preserves φ _ := (CategoryTheory.forget A).epi_of_epi_map
    ((epi_iff_surjective _).2 (surjective_app_of_epi_of_iso e φ))

end Concrete

instance preservesEpimorphisms_sheafSections_of_isSepClosed :
    ((sheafSections (Spec (.of k)).smallEtaleTopology AddCommGrpCat.{u + 1}).obj
      (op (etalePoint k))).PreservesEpimorphisms :=
  preservesEpimorphisms_sheafSections_of_iso (Iso.refl _)

instance preservesEpimorphisms_sheafSections_moduleCat_of_isSepClosed (Λ : Type (u + 1))
    [Ring Λ] : ((sheafSections (Spec (.of k)).smallEtaleTopology (ModuleCat.{u + 1} Λ)).obj
      (op (etalePoint k))).PreservesEpimorphisms :=
  preservesEpimorphisms_sheafSections_of_iso (Iso.refl _)

/-- Over a separably closed field `k`, the constant sheaf `ℤ` on the small étale site of
`Spec k` is projective. -/
instance projective_constantSheaf_of_isSepClosed :
    Projective ((constantSheaf (Spec (.of k)).smallEtaleTopology AddCommGrpCat.{u + 1}).obj
      (AddCommGrpCat.of (ULift ℤ))) :=
  @Adjunction.map_projective _ _ _ _ _ _ (constantSheafAdj _ _ isTerminalEtalePoint)
    (preservesEpimorphisms_sheafSections_of_isSepClosed k) _ AddCommGrpCat.projective_of_uliftInt

/-- Let `X` be a scheme isomorphic to `Spec k` for a separably closed field `k`, and let `Λ` be
a ring. The constant sheaf `Λ` on the small étale site of `X` is projective. -/
lemma projective_constantSheaf_moduleCat_of_iso {k} [Field k] [IsSepClosed k]
    {X : Scheme.{u}} (e : X ≅ Spec (.of k)) (Λ : Type (u + 1)) [Ring Λ] :
    Projective ((constantSheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ)).obj
      (ModuleCat.of Λ Λ)) :=
  @Adjunction.map_projective _ _ _ _ _ _
    (constantSheafAdj _ _ (MorphismProperty.Over.mkIdTerminal @AlgebraicGeometry.Etale X))
    (preservesEpimorphisms_sheafSections_of_iso e) _
    (ModuleCat.projective_of_categoryTheory_projective (ModuleCat.of Λ Λ))

/-- **Cohomology of `ℤ` on a geometric point.** For a separably closed field `k` (in
particular an algebraically closed one), `H^q(Spec k_ét, ℤ) = 0` for all `q ≥ 1`. -/
theorem subsingleton_H_constantSheaf_of_isSepClosed (q : ℕ) :
    Subsingleton (Sheaf.H ((constantSheaf (Spec (.of k)).smallEtaleTopology
      AddCommGrpCat.{u + 1}).obj (AddCommGrpCat.of (ULift ℤ))) (q + 1)) :=
  Abelian.Ext.subsingleton_of_projective _ _ _

end IsSepClosed

section Sections

open Limits

variable {k : Type u} [Field k] [IsSepClosed k]

variable {A : Type*} [Category A] {FA : A → A → Type*} {CA : A → Type*}
  [∀ X Y, FunLike (FA X Y) (CA X) (CA Y)] [ConcreteCategory A FA]
  [(Spec (.of k)).smallEtaleTopology.HasSheafCompose (CategoryTheory.forget A)]

/-- Over a separably closed field `k`, two sections of an étale sheaf on `Spec k` over an étale
`k`-scheme `U` are equal as soon as they agree after restriction along every morphism
`V ⟶ U` from an étale `k`-scheme `V ≅ Spec k`. -/
theorem eq_of_forall_restrict_eq_of_isSepClosed (F : Sheaf (Spec (.of k)).smallEtaleTopology A)
    {U : (Spec (.of k)).Etale} {x y : ToType (F.obj.obj (op U))}
    (h : ∀ (V : (Spec (.of k)).Etale) (_ : IsIso V.hom) (f : V ⟶ U),
      F.obj.map f.op x = F.obj.map f.op y) :
    x = y := by
  have : AlgebraicGeometry.Etale U.hom := U.prop
  let pts := {l : Spec (.of k) ⟶ U.left // l ≫ U.hom = 𝟙 _}
  let T : (Spec (.of k)).Etale := etalePoint k
  let g : ∀ l : pts, T ⟶ U := fun l ↦ MorphismProperty.Over.homMk (A := T) (B := U) l.1
    (l.2.trans rfl)
  refine Sheaf.isSeparated F U (Sieve.ofArrows (fun _ : pts ↦ T) g) ?_ x y ?_
  · rw [ofArrows_mem_smallEtaleTopology_iff]
    ext z
    simp only [Set.mem_iUnion, Set.mem_range, Set.mem_univ, iff_true]
    obtain ⟨l, hl, hz⟩ := exists_fac_of_etale_of_isSepClosed U.hom (𝟙 _) z
      (Subsingleton.elim (α := Spec (.of k)) _ _)
    exact ⟨⟨l, hl⟩, (default : Spec (.of k)), hz⟩
  · rintro V f ⟨W, f', _, ⟨l⟩, rfl⟩
    simp only [op_comp, Functor.map_comp, ConcreteCategory.comp_apply,
      h T (inferInstanceAs (IsIso (𝟙 (Spec (.of k)))))]

omit [IsSepClosed k] in
/-- An étale `k`-scheme `V` whose structure morphism is an isomorphism is isomorphic, in the
small étale site of `Spec k`, to the terminal object `𝟙 : Spec k ⟶ Spec k`. -/
noncomputable def etaleIsoOfIsIso (V : (Spec (.of k)).Etale) (hV : IsIso V.hom) :
    V ≅ etalePoint k :=
  MorphismProperty.Over.isoMk (@asIso _ _ _ _ V.hom hV) (Category.comp_id V.hom)

variable {Λ : Type (u + 1)} [Ring Λ]

/-- Over a separably closed field `k`, an étale sheaf of `Λ`-modules on `Spec k` whose global
sections vanish is zero. -/
theorem isZero_of_subsingleton_sections_of_isSepClosed
    (F : Sheaf (Spec (.of k)).smallEtaleTopology (ModuleCat.{u + 1} Λ))
    (h : Subsingleton (F.obj.obj (op (etalePoint k)))) : IsZero F := by
  have hU : ∀ U, Subsingleton (F.obj.obj (op U)) := fun U ↦ ⟨fun x y ↦
    eq_of_forall_restrict_eq_of_isSepClosed F fun V hV f ↦ by
      have : Subsingleton (F.obj.obj (op V)) :=
        (F.obj.mapIso (etaleIsoOfIsIso V hV).op).toLinearEquiv.toEquiv.symm.subsingleton
      exact Subsingleton.elim _ _⟩
  rw [IsZero.iff_id_eq_zero]
  ext U x
  exact Subsingleton.elim _ _

/-- The map `Λ_k ⟶ G` from the constant sheaf `Λ` on `Spec k` to an étale sheaf of
`Λ`-modules `G` corresponding to a global section `s` of `G`. -/
noncomputable def homOfGlobalSection
    {G : Sheaf (Spec (.of k)).smallEtaleTopology (ModuleCat.{u + 1} Λ)}
    (s : G.obj.obj (op (etalePoint k))) :
    (constantSheaf (Spec (.of k)).smallEtaleTopology (ModuleCat.{u + 1} Λ)).obj
      (ModuleCat.of Λ Λ) ⟶ G :=
  ((constantSheafAdj _ _ isTerminalEtalePoint).homEquiv
    _ _).symm (ModuleCat.ofHom (LinearMap.toSpanSingleton Λ _ s))

omit [IsSepClosed k] in
/-- Composing the map attached to a global section `s` with `ψ : G ⟶ G'` gives the map attached
to the global section `ψ(s)`. -/
theorem homOfGlobalSection_comp
    {G G' : Sheaf (Spec (.of k)).smallEtaleTopology (ModuleCat.{u + 1} Λ)}
    (s : G.obj.obj (op (etalePoint k))) (ψ : G ⟶ G') :
    homOfGlobalSection s ≫ ψ = homOfGlobalSection (ψ.hom.app _ s) := by
  rw [homOfGlobalSection, homOfGlobalSection, ← Adjunction.homEquiv_naturality_right_symm]
  congr 1
  ext
  simp

omit [IsSepClosed k] in
/-- The map attached to a nonzero global section is nonzero. -/
theorem homOfGlobalSection_ne_zero
    {G : Sheaf (Spec (.of k)).smallEtaleTopology (ModuleCat.{u + 1} Λ)}
    {s : G.obj.obj (op (etalePoint k))} (hs : s ≠ 0) : homOfGlobalSection s ≠ 0 := by
  intro h
  apply hs
  have := congrArg (fun f : (constantSheaf (Spec (.of k)).smallEtaleTopology
      (ModuleCat.{u + 1} Λ)).obj (ModuleCat.of Λ Λ) ⟶ G ↦ ModuleCat.Hom.hom
    (((constantSheafAdj (Spec (.of k)).smallEtaleTopology (ModuleCat.{u + 1} Λ)
      isTerminalEtalePoint).homEquiv (ModuleCat.of Λ Λ) G) f) (1 : Λ)) h
  simp only [homOfGlobalSection, Equiv.apply_symm_apply, Adjunction.homEquiv_unit, Functor.map_zero,
    comp_zero] at this
  simpa using this

end Sections

section Field

variable {K : Type u} [Field K]

/-- The terminal object `𝟙 : Spec K ⟶ Spec K` of the small étale site of `Spec K`. -/
local notation "𝟙ₖ" => MorphismProperty.Over.mk ⊤ (𝟙 (Spec (CommRingCat.of K)))
  (MorphismProperty.id_mem @AlgebraicGeometry.Etale (Spec (CommRingCat.of K)))

/-- A finite subset of `ℤ` which is closed under addition is contained in `{0}`. -/
private lemma eq_zero_of_finite_of_add_mem {S : Set (ULift.{u + 1} ℤ)} (hS : S.Finite)
    (hadd : ∀ a ∈ S, ∀ b ∈ S, a + b ∈ S) {a : ULift.{u + 1} ℤ} (ha : a ∈ S) : a = 0 := by
  by_contra h
  have hmem (n : ℕ) : (n + 1) • a ∈ S := by
    induction n with
    | zero => simpa using ha
    | succ n ih => simpa [add_smul, one_smul] using hadd _ ih _ ha
  refine Set.not_infinite.2 hS (Set.infinite_of_injective_forall_mem (f := fun n : ℕ ↦ (n + 1) • a)
    (fun n m hnm ↦ ?_) hmem)
  have hd : ((n : ℤ) + 1) * a.down = ((m : ℤ) + 1) * a.down := by
    simpa using congrArg ULift.down hnm
  have ha' : a.down ≠ 0 := fun h' ↦ h (ULift.ext h')
  exact_mod_cast add_right_cancel (mul_right_cancel₀ ha' hd)

open Algebra.TensorProduct TensorProduct in
/-- **Every `ℤ`-torsor on `Spec K` is trivial.** For a short exact sequence
`0 → ℤ → E → Q → 0` of abelian sheaves on the small étale site of the spectrum of a field `K`,
every global section of `Q` lifts to `E`. -/
theorem surjective_app_of_shortExact_constantSheaf_int
    {E Q : Sheaf (Spec (.of K)).smallEtaleTopology AddCommGrpCat.{u + 1}}
    (ι : (constantSheaf (Spec (.of K)).smallEtaleTopology AddCommGrpCat.{u + 1}).obj
      (AddCommGrpCat.of (ULift ℤ)) ⟶ E) (π : E ⟶ Q) (w : ι ≫ π = 0)
    (hS : (ShortComplex.mk ι π w).ShortExact) : Function.Surjective (π.hom.app (op 𝟙ₖ)) := by
  let M := AddCommGrpCat.of (ULift.{u + 1} ℤ)
  let P := (Spec (.of K)).pointFunctionSheaf M
  have hT := MorphismProperty.Over.mkIdTerminal @AlgebraicGeometry.Etale (Spec (.of K))
  have := (Spec (.of K)).isIso_constantSheafToPointFunctionSheaf M
    discreteTopology_of_etale_of_unique
  -- replace `ℤ` by the isomorphic sheaf `P: V ↦ (V → ℤ)` of functions on points
  let ι' : P ⟶ E := inv ((Spec (.of K)).constantSheafToPointFunctionSheaf M) ≫ ι
  have w' : ι' ≫ π = 0 := by simp [ι', w]
  have hS' : (ShortComplex.mk ι' π w').ShortExact :=
    ShortComplex.shortExact_of_iso (S₁ := ShortComplex.mk ι π w) (ShortComplex.isoMk
      (asIso ((Spec (.of K)).constantSheafToPointFunctionSheaf M)) (Iso.refl _) (Iso.refl _)
      (by simp [ι']) (by simp)) hS
  have := hS'.mono_f
  have := hS'.epi_g
  have (U : (Spec (.of K)).Etaleᵒᵖ) : Limits.PreservesLimits
      ((sheafSections (Spec (.of K)).smallEtaleTopology AddCommGrpCat.{u + 1}).obj U) :=
    inferInstanceAs
      (Limits.PreservesLimits (sheafToPresheaf _ _ ⋙ (CategoryTheory.evaluation _ _).obj U))
  have hι (U) : Function.Injective (ι'.hom.app U) :=
    (AddCommGrpCat.mono_iff_injective _).1
      (((sheafSections (Spec (.of K)).smallEtaleTopology AddCommGrpCat.{u + 1}).obj U).map_mono ι')
  have hexact (U) (x : E.obj.obj U) (hx : π.hom.app U x = 0) : ∃ g, ι'.hom.app U g = x :=
    (ShortComplex.ab_exact_iff _).1 (hS'.exact.map_of_mono_of_preservesKernel
      ((sheafSections (Spec (.of K)).smallEtaleTopology AddCommGrpCat.{u + 1}).obj U)
      hS'.mono_f inferInstance) x hx
  have := (Sheaf.isLocallySurjective_iff_epi' (A := AddCommGrpCat.{u + 1}) π).2 inferInstance
  intro q
  obtain ⟨L, _, _, _, f, e, he⟩ := exists_etaleSpec_field_mem_of_mem_smallEtaleTopology _
    (Presheaf.imageSieve_mem (Spec (.of K)).smallEtaleTopology π.hom (U := op 𝟙ₖ) q)
  refine exists_app_eq_of_compatible π L f q e he ?_
  -- the difference of two pullbacks of `e` is a section of `P`
  have hπ {Z : (Spec (.of K)).Etale} (g₁ g₂ : Z ⟶ etaleSpec K L) :
      π.hom.app _ (E.obj.map g₁.op e - E.obj.map g₂.op e) = 0 := by
    rw [map_sub, NatTrans.naturality_apply, NatTrans.naturality_apply, he,
      ← ConcreteCategory.comp_apply, ← ConcreteCategory.comp_apply, ← Functor.map_comp,
      ← Functor.map_comp, ← op_comp, ← op_comp, hT.hom_ext (g₁ ≫ f) (g₂ ≫ f), sub_self]
  choose c hc using fun (Z : (Spec (.of K)).Etale) (g₁ g₂ : Z ⟶ etaleSpec K L) ↦
    hexact _ _ (hπ g₁ g₂)
  have hc_map {Z Z' : (Spec (.of K)).Etale} (h : Z' ⟶ Z) (g₁ g₂ : Z ⟶ etaleSpec K L) :
      P.obj.map h.op (c Z g₁ g₂) = c Z' (h ≫ g₁) (h ≫ g₂) := by
    apply hι
    rw [NatTrans.naturality_apply, hc, hc, map_sub, ← ConcreteCategory.comp_apply,
      ← ConcreteCategory.comp_apply, ← Functor.map_comp, ← Functor.map_comp, ← op_comp,
      ← op_comp]
  have hc_add {Z : (Spec (.of K)).Etale} (g₁ g₂ g₃ : Z ⟶ etaleSpec K L) :
      c Z g₁ g₃ = c Z g₁ g₂ + c Z g₂ g₃ := by
    apply hι
    rw [map_add, hc, hc, hc]
    abel
  -- the Čech cocycle on `Spec (L ⊗_K L)`, a function on a finite set of points
  let i₁ : etaleSpec K (L ⊗[K] L) ⟶ etaleSpec K L := etaleSpecMap includeLeft
  let i₂ : etaleSpec K (L ⊗[K] L) ⟶ etaleSpec K L := etaleSpecMap includeRight
  let c₀ : (etaleSpec K (L ⊗[K] L)).left → ULift.{u + 1} ℤ := c _ i₁ i₂
  have : Module.Finite K L := Algebra.FormallyUnramified.finite_of_free K L
  have : IsArtinianRing (L ⊗[K] L) := IsArtinianRing.of_finite K _
  have hfin : Finite (etaleSpec K (L ⊗[K] L)).left :=
    inferInstanceAs (Finite (PrimeSpectrum (L ⊗[K] L)))
  have hadd : ∀ a ∈ Set.range c₀, ∀ b ∈ Set.range c₀, a + b ∈ Set.range c₀ := by
    rintro _ ⟨w₁, rfl⟩ _ ⟨w₂, rfl⟩
    obtain ⟨Z, p₁, p₂, z, hp, rfl, rfl⟩ := exists_eq_of_apply_eq i₂ i₁ w₁ w₂
      (@Subsingleton.elim (Spec (.of L)) _ _ _)
    obtain ⟨h, hh₁, hh₂⟩ := exists_comp_etaleSpecMap_includeLeft_eq (p₁ ≫ i₁) (p₂ ≫ i₂)
    refine ⟨h.left z, ?_⟩
    have e₁ : c Z (p₁ ≫ i₁) (p₂ ≫ i₂) = P.obj.map h.op c₀ := by
      have := hc_map h i₁ i₂
      rw [hh₁, hh₂] at this
      exact this.symm
    have e₂ : c Z (p₁ ≫ i₁) (p₁ ≫ i₂) = P.obj.map p₁.op c₀ := (hc_map _ _ _).symm
    have e₃ : c Z (p₁ ≫ i₂) (p₂ ≫ i₂) = P.obj.map p₂.op c₀ := by
      rw [hp]
      exact (hc_map _ _ _).symm
    have := hc_add (p₁ ≫ i₁) (p₁ ≫ i₂) (p₂ ≫ i₂)
    rw [e₁, e₂, e₃] at this
    exact congrFun this z
  have hc₀ : c₀ = 0 := funext fun w ↦ eq_zero_of_finite_of_add_mem (Set.finite_range c₀) hadd
    ⟨w, rfl⟩
  intro Z g₁ g₂
  obtain ⟨h, rfl, rfl⟩ := exists_comp_etaleSpecMap_includeLeft_eq g₁ g₂
  have h₀ : c Z (h ≫ i₁) (h ≫ i₂) = 0 := by
    rw [← hc_map]
    change P.obj.map h.op c₀ = 0
    rw [hc₀, map_zero]
  rw [← sub_eq_zero, ← hc, h₀, map_zero]

variable (K) in
/-- **`H¹` of `ℤ` on the spectrum of a field vanishes.** For every field `K`,
`H¹(Spec K_ét, ℤ) = 0`. -/
theorem subsingleton_H_one_constantSheaf_of_field :
    Subsingleton (Sheaf.H ((constantSheaf (Spec (.of K)).smallEtaleTopology
      AddCommGrpCat.{u + 1}).obj (AddCommGrpCat.of (ULift ℤ))) 1) :=
  Sheaf.subsingleton_H_one_of_surjective _
    (MorphismProperty.Over.mkIdTerminal @AlgebraicGeometry.Etale (Spec (.of K)))
    (fun _ _ ι π w hS ↦ surjective_app_of_shortExact_constantSheaf_int ι π w hS)

end Field

/-- **`H¹` of `ℤ` on the spectrum of a field vanishes.** For every field `K`,
`H¹(Spec K_ét, ℤ) = 0`; version of
`AlgebraicGeometry.Scheme.subsingleton_H_one_constantSheaf_of_field` for a commutative ring
which is a field. -/
theorem subsingleton_H_one_constantSheaf_of_isField (K : CommRingCat.{u}) (hK : IsField K) :
    Subsingleton (Sheaf.H ((constantSheaf (Spec K).smallEtaleTopology
      AddCommGrpCat.{u + 1}).obj (AddCommGrpCat.of (ULift ℤ))) 1) := by
  let := hK.toField
  exact subsingleton_H_one_constantSheaf_of_field K

end AlgebraicGeometry.Scheme
