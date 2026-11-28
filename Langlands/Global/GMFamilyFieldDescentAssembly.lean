import Langlands.Global.GMFamilyFieldDescentStatement
import Langlands.Global.GMFamilyFieldDescentSpecial
import Langlands.GroupScheme.Rational.FieldLeviSplitComponentStatement
import Langlands.GroupScheme.Rational.LeviSplitComponentRootDatumStatement
import Langlands.GroupScheme.Reductive.FieldExtensionProof
import Langlands.GroupScheme.Rational.CharacterRestrictionProof

/-! # Field-extension descent from its group-theoretic inputs -/

noncomputable section

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry TensorProduct
open scoped CategoryTheory.MonObj RealInnerProductSpace
open Classical

namespace Langlands.GMFamily

open Langlands.GroupScheme Langlands.GroupScheme.RealTorusSpace FieldDescentTori

section RootVectors

variable {k : Type u} [Field k] {A : CommGroupScheme (Spec (CommRingCat.of k))}
  {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]

theorem inner_rootVectorIn (e : V A ≃ₗ[ℝ] E) (χ : characterLattice A) (x : E) :
    ⟪rootVectorIn e χ, x⟫ = eval A χ (e.symm x) := by
  rw [rootVectorIn, InnerProductSpace.toDual_symm_apply]
  rfl

theorem rootVectorIn_injective (hA : IsSplitTorus A.toGrp) (e : V A ≃ₗ[ℝ] E) :
    Function.Injective (rootVectorIn (A := A) e) := by
  intro χ χ' h
  apply eval_injective hA
  apply LinearMap.ext
  intro x
  rw [← e.symm_apply_apply x, ← inner_rootVectorIn, h, inner_rootVectorIn]

theorem rootVectorIn_eq_zero_iff (hA : IsSplitTorus A.toGrp) (e : V A ≃ₗ[ℝ] E)
    {χ : characterLattice A} : rootVectorIn e χ = 0 ↔ χ = 0 := by
  have h0 : rootVectorIn e (0 : characterLattice A) = 0 := by
    apply ext_inner_right ℝ
    intro x
    rw [inner_rootVectorIn, eval_zero, inner_zero_left]
    rfl
  rw [← h0, (rootVectorIn_injective hA e).eq_iff]

variable {G : GroupScheme (Spec (CommRingCat.of k))} [IsAffineHom G.X.hom]
  [LocallyOfFiniteType G.X.hom]

theorem mem_actualRootVectors {i : A.toGrp ⟶ G} {hA : IsSplitTorus A.toGrp} {e : V A ≃ₗ[ℝ] E}
    {x : E} : x ∈ actualRootVectors i hA e ↔ ∃ α ∈ roots i, rootVectorIn e α = x := by
  unfold actualRootVectors
  rw [Finset.mem_image]
  simp only [Set.Finite.mem_toFinset, relativeRoots_eq_roots]

end RootVectors

section FineRoots

variable {K : Type u} [Field K] {G : GroupScheme (Spec (CommRingCat.of K))} [IsAffineHom G.X.hom]
  [LocallyOfFiniteType G.X.hom]
  {A₁ T : CommGroupScheme (Spec (CommRingCat.of K))} [FiniteDimensional ℝ (V A₁)]

open FieldDescentData RootRestriction

theorem res_rv_eval (D : FieldDescentData (V A₁) (V T)) (g : A₁ ⟶ T)
    (hκ : D.κ = cocharacterMapReal g) (δ : characterLattice T) :
    res D.φ (D.rv (eval T δ)) = rootVectorIn D.e₁ (g ≫ δ) := by
  rw [D.res_rv, rootVectorIn, hκ, eval_comp_cocharacterMapReal]

/-- **The fine roots in the Euclidean coordinates.** The restricted roots of linear-algebra
descent data built from a split torus `T` through which `A₁` factors are the Riesz vectors of
the roots of `A₁`. -/
theorem R_eq_actualRootVectors (hA₁ : IsSplitTorus A₁.toGrp) (hT : IsSplitTorus T.toGrp)
    (t : T.toGrp ⟶ G) (g : A₁ ⟶ T) (D : FieldDescentData (V A₁) (V T))
    (hκ : D.κ = cocharacterMapReal g) (hroots : D.roots = rootFunctionals hT t) :
    D.R = actualRootVectors (CommGroupScheme.groupHom g ≫ t) hA₁ D.e₁ := by
  ext α
  rw [D.mem_R, mem_actualRootVectors]
  constructor
  · rintro ⟨hα, c, hc, rfl⟩
    rw [hroots, rootFunctionals, Finset.mem_image] at hc
    obtain ⟨δ, hδ, rfl⟩ := hc
    rw [res_rv_eval D g hκ] at hα ⊢
    refine ⟨g ≫ δ, ?_, rfl⟩
    rw [Set.Finite.mem_toFinset, relativeRoots_eq_roots] at hδ
    refine (mem_roots_comp_iff hT hA₁ g t _).mpr ⟨?_, δ, hδ, rfl⟩
    intro h0
    exact hα ((rootVectorIn_eq_zero_iff hA₁ D.e₁).mpr h0)
  · rintro ⟨α', hα', rfl⟩
    obtain ⟨hne, δ, hδ, rfl⟩ := (mem_roots_comp_iff hT hA₁ g t _).mp hα'
    refine ⟨fun h0 => hne ((rootVectorIn_eq_zero_iff hA₁ D.e₁).mp h0), eval T δ, ?_,
      res_rv_eval D g hκ δ⟩
    rw [hroots, rootFunctionals]
    exact Finset.mem_image_of_mem _ ((Set.Finite.mem_toFinset _).mpr hδ)

end FineRoots

section Coarse

variable {k K : Type u} [Field k] [Field K] [Algebra k K]
  {A : CommGroupScheme (Spec (CommRingCat.of k))} {A₁ : CommGroupScheme (Spec (CommRingCat.of K))}
  {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]

local notation "bmap" => algebraBaseMap k K

/-- Orthogonal projection to the coarse coordinates sends the vector of a fine character to the
vector of the coarse character it restricts to. -/
theorem restrictedRoot_rootVectorIn (j : (CommGroupScheme.baseChange bmap).obj A ⟶ A₁)
    (e₁ : V A₁ ≃ₗ[ℝ] E) (b : Submodule ℝ E) (e : V A ≃ₗ[ℝ] b)
    (he : ∀ x, (e x : E) = e₁ (fieldCocharacterInclusion j x)) {α : characterLattice A₁}
    {β : characterLattice A} (h : j ≫ α = characterLattice.baseChange bmap A β) :
    restrictedRoot b (rootVectorIn e₁ α) = rootVectorIn e β := by
  apply ext_inner_right ℝ
  intro y
  obtain ⟨x, rfl⟩ := e.surjective y
  rw [inner_rootVectorIn e, LinearEquiv.symm_apply_apply, restrictedRoot,
    Submodule.inner_orthogonalProjectionOnto_eq_of_mem_right, he, inner_rootVectorIn e₁,
    LinearEquiv.symm_apply_apply, eval_fieldCocharacterInclusion_of_eq j h]

variable {G : GroupScheme (Spec (CommRingCat.of k))} [IsAffineHom G.X.hom]
  [LocallyOfFiniteType G.X.hom]

local instance fieldDescentAssemblyAffine :
    IsAffineHom ((GroupScheme.baseChange (algebraBaseMap k K)).obj G).X.hom := by
  change IsAffineHom (pullback.snd G.X.hom (algebraBaseMap k K))
  infer_instance

local instance fieldDescentAssemblyFiniteType :
    LocallyOfFiniteType ((GroupScheme.baseChange (algebraBaseMap k K)).obj G).X.hom := by
  change LocallyOfFiniteType (pullback.snd G.X.hom (algebraBaseMap k K))
  infer_instance

/-- **The coarse roots are the nonzero projections of the fine roots.** -/
theorem image_restrictedRoot_erase (hAs : IsSplitTorus A.toGrp) (hA₁ : IsSplitTorus A₁.toGrp)
    (j : (CommGroupScheme.baseChange bmap).obj A ⟶ A₁) (i : A.toGrp ⟶ G)
    (i₁ : A₁.toGrp ⟶ (GroupScheme.baseChange bmap).obj G)
    (hcomp : (GroupScheme.baseChange bmap).map i = CommGroupScheme.groupHom j ≫ i₁)
    (e₁ : V A₁ ≃ₗ[ℝ] E) (b : Submodule ℝ E) (e : V A ≃ₗ[ℝ] b)
    (he : ∀ x, (e x : E) = e₁ (fieldCocharacterInclusion j x)) :
    ((actualRootVectors i₁ hA₁ e₁).image (restrictedRoot b)).erase 0 =
      actualRootVectors i hAs e := by
  ext x
  rw [Finset.mem_erase, Finset.mem_image, mem_actualRootVectors]
  simp only [mem_actualRootVectors]
  constructor
  · rintro ⟨hx, _, ⟨α, hα, rfl⟩, rfl⟩
    have h0 : j ≫ α ≠ 0 := by
      intro h0
      apply hx
      rw [restrictedRoot_rootVectorIn j e₁ b e he (β := 0) (by rw [h0, map_zero])]
      exact (rootVectorIn_eq_zero_iff hAs e).mpr rfl
    obtain ⟨β, hβ, hβe⟩ := exists_coarse_of_mem_roots hAs hA₁ j i i₁ hcomp hα h0
    exact ⟨β, hβ, (restrictedRoot_rootVectorIn j e₁ b e he hβe).symm⟩
  · rintro ⟨β, hβ, rfl⟩
    obtain ⟨α, hα, hαe⟩ := exists_fine_of_mem_roots hAs hA₁ j i i₁ hcomp hβ
    refine ⟨?_, _, ⟨α, hα, rfl⟩, restrictedRoot_rootVectorIn j e₁ b e he hαe⟩
    rw [Ne, rootVectorIn_eq_zero_iff hAs e]
    rintro rfl
    exact (mem_roots.mp hβ).1 rfl

variable {M : GroupScheme (Spec (CommRingCat.of k))} {M₁ : GroupScheme (Spec (CommRingCat.of K))}

/-- **Parameter compatibility in Euclidean coordinates.** If the coarse coordinates are the
image of the coarse cocharacters and are orthogonal to the common kernel of the fine restrictions
of the rational characters, then evaluation of these restrictions factors through the
orthogonal projection to the coarse coordinates. -/
theorem isFieldParameterCompatible_of (a : A.toGrp ⟶ M) (a₁ : A₁.toGrp ⟶ M₁)
    (m : M₁ ⟶ (GroupScheme.baseChange bmap).obj M)
    (j : (CommGroupScheme.baseChange bmap).obj A ⟶ A₁)
    (hj : CommGroupScheme.groupHom j ≫ a₁ ≫ m = (GroupScheme.baseChange bmap).map a)
    (e₁ : V A₁ ≃ₗ[ℝ] E) (b : Submodule ℝ E) (e : V A ≃ₗ[ℝ] b)
    (he : ∀ x, (e x : E) = e₁ (fieldCocharacterInclusion j x))
    (hcompl : IsCompl (LinearMap.range (fieldCocharacterInclusion j)) (fineKernel a₁ m))
    (horth : ∀ x, ∀ y ∈ fineKernel a₁ m, ⟪e₁ (fieldCocharacterInclusion j x), e₁ y⟫ = 0) :
    IsFieldParameterCompatible m a a₁ b e e₁ := by
  intro χ x
  obtain ⟨u, rfl⟩ := e₁.surjective x
  have hu : u ∈ LinearMap.range (fieldCocharacterInclusion j) ⊔ fineKernel a₁ m := by
    rw [hcompl.sup_eq_top]
    exact Submodule.mem_top
  obtain ⟨_, ⟨w, rfl⟩, z, hz, rfl⟩ := Submodule.mem_sup.mp hu
  have hzb : e₁ z ∈ bᗮ := by
    rw [Submodule.mem_orthogonal]
    intro v hv
    obtain ⟨w', hw'⟩ := e.surjective ⟨v, hv⟩
    have hv' : v = e₁ (fieldCocharacterInclusion j w') := by
      rw [← he, hw']
    rw [hv']
    exact horth w' z hz
  have hproj : b.orthogonalProjectionOnto (e₁ (fieldCocharacterInclusion j w + z)) = e w := by
    rw [map_add, map_add, ← he, Submodule.orthogonalProjectionOnto_mem_subspace_eq_self,
      (Submodule.orthogonalProjectionOnto_eq_zero_iff).mpr hzb, add_zero]
  rw [LinearEquiv.symm_apply_apply, hproj, LinearEquiv.symm_apply_apply, map_add]
  have h1 := eval_fineCharacter_inclusion a a₁ m j hj χ w
  have h2 := mem_fineKernel.mp hz χ
  simp only [fineCharacter] at h1 h2
  rw [h1, h2, add_zero]

variable [IsAffineHom M.X.hom]

/-- **Special weight sums in Euclidean coordinates.** If every vector orthogonal to the common
kernel of the fine restrictions of rational characters lies in the coarse coordinates, then the
multiplicity-weighted fibre sums of the fine roots lie there. -/
theorem hasSpecialWeightSums_of (h2 : LeviWeightFibreDeterminantStatement.{u}) (l : M ⟶ G)
    (a : A.toGrp ⟶ M) (hAs : IsSplitTorus A.toGrp) (hAc : IsCentral a)
    (hA₁ : IsSplitTorus A₁.toGrp) (a₁ : A₁.toGrp ⟶ M₁)
    (m : M₁ ⟶ (GroupScheme.baseChange bmap).obj M)
    (j : (CommGroupScheme.baseChange bmap).obj A ⟶ A₁)
    (hj : CommGroupScheme.groupHom j ≫ a₁ ≫ m = (GroupScheme.baseChange bmap).map a)
    (e₁ : V A₁ ≃ₗ[ℝ] E) (b : Submodule ℝ E) (e : V A ≃ₗ[ℝ] b)
    (he : ∀ x, (e x : E) = e₁ (fieldCocharacterInclusion j x))
    (hb : ∀ v : E, (∀ y ∈ fineKernel a₁ m, ⟪v, e₁ y⟫ = 0) → v ∈ b) :
    HasSpecialWeightSums ((a₁ ≫ m) ≫ (GroupScheme.baseChange bmap).map l) hA₁ e₁ b := by
  intro β hβ
  apply hb
  intro y hy
  rw [sum_inner]
  simp only [real_inner_smul_left, inner_rootVectorIn, LinearEquiv.symm_apply_apply]
  by_cases hne : ((hA₁.finite_relativeRoots
      ((a₁ ≫ m) ≫ (GroupScheme.baseChange bmap).map l)).toFinset.filter
        (fun α => restrictedRoot b (rootVectorIn e₁ α) = β)).Nonempty
  · obtain ⟨α₀, hα₀⟩ := hne
    obtain ⟨-, hα₀β⟩ := Finset.mem_filter.mp hα₀
    obtain ⟨β₀, hβ₀⟩ :=
      (hAs.characterLattice_baseChange_bijective bmap A).surjective (j ≫ α₀)
    have hrβ := restrictedRoot_rootVectorIn j e₁ b e he hβ₀.symm
    have hβ₀ne : β₀ ≠ 0 := by
      rintro rfl
      apply hβ
      rw [← hα₀β, hrβ]
      exact (rootVectorIn_eq_zero_iff hAs e).mpr rfl
    have hfil : (hA₁.finite_relativeRoots
        ((a₁ ≫ m) ≫ (GroupScheme.baseChange bmap).map l)).toFinset.filter
          (fun α => restrictedRoot b (rootVectorIn e₁ α) = β) =
        (hA₁.finite_relativeRoots
          ((a₁ ≫ m) ≫ (GroupScheme.baseChange bmap).map l)).toFinset.filter
          (fun α => j ≫ α = characterLattice.baseChange bmap A β₀) := by
      apply Finset.filter_congr
      intro α _
      obtain ⟨β', hβ'⟩ :=
        (hAs.characterLattice_baseChange_bijective bmap A).surjective (j ≫ α)
      rw [restrictedRoot_rootVectorIn j e₁ b e he hβ'.symm, ← hα₀β, hrβ,
        (rootVectorIn_injective hAs e).eq_iff, ← hβ']
      exact ((hAs.characterLattice_baseChange_bijective bmap A).injective.eq_iff).symm
    rw [hfil]
    exact fibre_sum_eq_zero h2 l a hAs hAc hA₁ a₁ m j hj hβ₀ne hy
  · rw [Finset.not_nonempty_iff_eq_empty.mp hne, Finset.sum_empty]

end Coarse

section Main

variable {k K : Type u} [Field k] [Field K] [Algebra k K]
  {G : GroupScheme (Spec (CommRingCat.of k))} [IsAffineHom G.X.hom] [LocallyOfFiniteType G.X.hom]

local instance fieldDescentMainAffine :
    IsAffineHom ((GroupScheme.baseChange (algebraBaseMap k K)).obj G).X.hom := by
  change IsAffineHom (pullback.snd G.X.hom (algebraBaseMap k K))
  infer_instance

local instance fieldDescentMainFiniteType :
    LocallyOfFiniteType ((GroupScheme.baseChange (algebraBaseMap k K)).obj G).X.hom := by
  change LocallyOfFiniteType (pullback.snd G.X.hom (algebraBaseMap k K))
  infer_instance

/-- **Field-extension descent for nested rational Levis, from the group-theoretic inputs.** -/
theorem hasActualFieldDescent_of_inputs (h2 : LeviWeightFibreDeterminantStatement.{u})
    (h3 : LeviSplitComponentRootDatumStatement.{u}) (hG : IsConnectedReductive G)
    {P M : GroupScheme (Spec (CommRingCat.of k))} {p : P ⟶ G} {l : M ⟶ P}
    (hl : IsRationalLeviSubgroup l)
    {P₁ M₁ : GroupScheme (Spec (CommRingCat.of K))}
    {p₁ : P₁ ⟶ (GroupScheme.baseChange (algebraBaseMap k K)).obj G} {l₁ : M₁ ⟶ P₁}
    (hP₁ : IsParabolicSubgroup p₁) (hl₁ : IsRationalLeviSubgroup l₁)
    {m : M₁ ⟶ (GroupScheme.baseChange (algebraBaseMap k K)).obj M}
    (hm : m ≫ (GroupScheme.baseChange (algebraBaseMap k K)).map (l ≫ p) = l₁ ≫ p₁)
    {A : CommGroupScheme (Spec (CommRingCat.of k))} {a : A.toGrp ⟶ M} (hA : IsSplitComponent a)
    {A₁ : CommGroupScheme (Spec (CommRingCat.of K))} {a₁ : A₁.toGrp ⟶ M₁}
    (hA₁ : IsSplitComponent a₁) (j : (CommGroupScheme.baseChange (algebraBaseMap k K)).obj A ⟶ A₁)
    (hj : CommGroupScheme.groupHom j ≫ a₁ ≫ m =
      (GroupScheme.baseChange (algebraBaseMap k K)).map a) :
    HasActualFieldDescent (l ≫ p) (l₁ ≫ p₁) m a hA a₁ hA₁ := by
  have : IsAffineHom M.X.hom := hl.isConnectedReductive.isAffineHom
  have hGK : IsConnectedReductive ((GroupScheme.baseChange (algebraBaseMap k K)).obj G) :=
    connectedReductiveFieldExtensionStatement k K G hG
  obtain ⟨T, t, g, hT, hgt, hinj, hrange, hcor⟩ :=
    h3 K _ hGK P₁ M₁ p₁ l₁ hP₁ hl₁ A₁ a₁ hA₁
  have hAs : IsSplitTorus A.toGrp := hA.isCentralSplitTorus.isSplitSubtorus.1
  have hAc : IsCentral a := hA.isCentralSplitTorus.isCentral
  have hA₁s : IsSplitTorus A₁.toGrp := hA₁.isCentralSplitTorus.isSplitSubtorus.1
  obtain ⟨hres_inj, hres_fin⟩ := characterRestriction k M hl.isConnectedReductive A a hA
  have hcompl := isCompl_fineKernel a a₁ m j hj hAs hA₁s hres_inj hres_fin
  have hι := fieldCocharacterInclusion_injective a a₁ m j hj hAs hres_fin
  have hfine : (a₁ ≫ m) ≫ (GroupScheme.baseChange (algebraBaseMap k K)).map (l ≫ p) =
      a₁ ≫ l₁ ≫ p₁ := by
    rw [Category.assoc, hm]
  have hgt' : (a₁ ≫ m) ≫ (GroupScheme.baseChange (algebraBaseMap k K)).map (l ≫ p) =
      CommGroupScheme.groupHom g ≫ t := by
    rw [hfine, hgt]
  have hcomp : (GroupScheme.baseChange (algebraBaseMap k K)).map (a ≫ l ≫ p) =
      CommGroupScheme.groupHom j ≫ a₁ ≫ l₁ ≫ p₁ := by
    exact (Functor.map_comp _ _ _).trans ((congrArg
      (· ≫ (GroupScheme.baseChange (algebraBaseMap k K)).map (l ≫ p)) hj.symm).trans
        ((Category.assoc _ _ _).trans (congrArg (CommGroupScheme.groupHom j ≫ ·) hfine)))
  have : FiniteDimensional ℝ (V A₁) := hA₁s.finite_realCocharacterSpace
  let D := torusData hT t g hinj hrange hcor _ _ hcompl
    (fun c _ hβ y hy => torus_special h2 (l ≫ p) a hAs hAc hA₁s a₁ m j hj hT t g hgt' c hβ y hy)
  let e : V A ≃ₗ[ℝ] D.b := (LinearEquiv.ofInjective _ hι).trans
    (Submodule.equivMapOfInjective D.e₁.toLinearMap D.e₁.injective
      (LinearMap.range (fieldCocharacterInclusion j)))
  have he : ∀ x, (e x : EuclideanSpace ℝ (Fin (Module.finrank ℝ (V A₁)))) =
      D.e₁ (fieldCocharacterInclusion j x) := fun _ => rfl
  have hR : actualRootVectors (a₁ ≫ l₁ ≫ p₁) hA₁s D.e₁ = D.R := by
    rw [← hgt]
    exact (R_eq_actualRootVectors hA₁s hT t g D rfl rfl).symm
  have hpar : IsFieldParameterCompatible m a a₁ D.b e D.e₁ :=
    isFieldParameterCompatible_of a a₁ m j hj D.e₁ D.b e he hcompl
      (fun x y hy => D.inner_e₁_B_K ⟨x, rfl⟩ hy)
  have hcentral : ∀ x : D.b,
      ((centralSpace (actualRootVectors (a₁ ≫ l₁ ≫ p₁) hA₁s D.e₁)).orthogonalProjectionOnto
        (x : EuclideanSpace ℝ (Fin (Module.finrank ℝ (V A₁)))) :
          EuclideanSpace ℝ (Fin (Module.finrank ℝ (V A₁)))) ∈ D.b := by
    intro x
    rw [hR, ← Submodule.starProjection_apply]
    exact D.starProjection_mem_b x.2
  have hspecial : HasSpecialWeightSums (a₁ ≫ l₁ ≫ p₁) hA₁s D.e₁ D.b := by
    have h := hasSpecialWeightSums_of h2 (l ≫ p) a hAs hAc hA₁s a₁ m j hj D.e₁ D.b e he
      (fun v hv => D.mem_b_of_orthogonal hv)
    rwa [hfine] at h
  have hformula : HasFieldDescentFormula (actualRootVectors (a₁ ≫ l₁ ≫ p₁) hA₁s D.e₁) D.b := by
    rw [hR]
    exact D.hasFieldDescentFormula
  unfold HasActualFieldDescent
  refine ⟨j, hj, D.e₁, D.b, e, he, hpar, ?_, hcentral, hspecial, hformula⟩
  convert image_restrictedRoot_erase hAs hA₁s j (a ≫ l ≫ p) (a₁ ≫ l₁ ≫ p₁) hcomp D.e₁ D.b e he

end Main

/-- **Arthur 2005, Lemma 17.5 (field-extension case), from the group-theoretic inputs.** -/
theorem fieldExtensionDescent_of_inputs (h1 : FieldLeviSplitComponentInclusionStatement.{u})
    (h2 : LeviWeightFibreDeterminantStatement.{u})
    (h3 : LeviSplitComponentRootDatumStatement.{u}) :
    FieldExtensionDescentStatement.{u} := by
  intro k K _ _ _ _ G _ _ hG f BC P M p l hP hl P₁ M₁ p₁ l₁ hP₁ hl₁ m hm A a hA A₁ a₁ hA₁
  obtain ⟨j, hj⟩ := h1 k K G hG P M p l hP hl P₁ M₁ p₁ l₁ hP₁ hl₁ m hm A a hA A₁ a₁ hA₁
  exact hasActualFieldDescent_of_inputs h2 h3 hG hl hP₁ hl₁ hm hA hA₁ j hj

end Langlands.GMFamily
