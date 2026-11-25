/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import Mathlib.CategoryTheory.Sites.DenseSubsite.SheafEquiv
public import WeilConjectures.AlgebraicGeometry.Sites.ProetaleTopologicalInvariance.AffineModelBaseChange
public import WeilConjectures.AlgebraicGeometry.Sites.ProetaleTopologicalInvariance.AffineModelCover
public import WeilConjectures.AlgebraicGeometry.Sites.ProetaleTopologicalInvariance.Covers
public import WeilConjectures.RingTheory.ProEtale.WeaklyEtaleUniversalHomeomorphism
public import WeilConjectures.Mathlib.CategoryTheory.Sites.Sieves

/-!
# Topological invariance of the small pro-étale site

Let `r : X ⟶ Y` be a universal homeomorphism. Base change along `r`,
`MorphismProperty.Over.pullback @WeaklyEtale ⊤ r : Y.ProEt ⥤ X.ProEt`, exhibits the small
pro-étale site of `Y` as a dense subsite of the small pro-étale site of `X`, so that restriction
along it is an equivalence of categories of sheaves.

This is the pro-étale analogue of [Stacks 04DZ]. We do not prove that base change is an
equivalence of the underlying categories (its essential surjectivity would need that a
quasi-affine scheme with an affine universally homeomorphic cover is affine); the comparison
lemma only needs the following local statements.

* Coverings are preserved and reflected
  (`AlgebraicGeometry.Scheme.ProEt.functorPushforward_overPullback_mem_topology_iff`) and base
  change is locally faithful (`AlgebraicGeometry.Scheme.ProEt.isLocallyFaithful_overPullback`).
* Base change is cover dense (`AlgebraicGeometry.Scheme.ProEt.isCoverDense_overPullback`):
  every weakly étale `X`-scheme is covered by base changes of ind-étale affine `Y`-schemes, by the
  local descent of weakly étale algebras `Algebra.WeaklyEtale.exists_indEtale_baseChange`.
* Base change is locally full (`AlgebraicGeometry.Scheme.ProEt.isLocallyFull_overPullback`):
  between base changes of ind-étale affine models over the same affine open it is full
  (`AlgebraicGeometry.Scheme.ProEt.exists_overPullback_map_eq_of_indEtale`), and every morphism
  is locally of this form.

## Main statements

* `AlgebraicGeometry.Scheme.ProEt.isDenseSubsite_overPullback`: base change along a universal
  homeomorphism is a dense subsite.
-/

@[expose] public section

universe u

open CategoryTheory Limits

namespace AlgebraicGeometry.Scheme.ProEt

variable {X Y : Scheme.{u}} (r : X ⟶ Y) [IsUniversalHomeomorphism r]

/-- The affine opens of `X` of the form `r ⁻¹ᵁ U` with `U` an affine open of `Y`. -/
def preimageAffineOpens : Set X.Opens :=
  {W | ∃ U : Y.Opens, IsAffineOpen U ∧ W = r ⁻¹ᵁ U}

lemma isAffineOpen_of_mem_preimageAffineOpens (W : X.Opens) (hW : W ∈ preimageAffineOpens r) :
    IsAffineOpen W := by
  obtain ⟨U, hU, rfl⟩ := hW
  exact hU.preimage r

/-- The preimages of the affine opens of `Y` form a basis of `X`, `r` being a homeomorphism. -/
lemma isBasis_preimageAffineOpens : TopologicalSpace.Opens.IsBasis (preimageAffineOpens r) := by
  rw [TopologicalSpace.Opens.isBasis_iff_nbhd]
  intro W x hx
  have hr := r.isHomeomorph
  let O : Y.Opens := ⟨r.base '' W, hr.isOpenMap _ W.2⟩
  have hxO : r.base x ∈ O := ⟨x, hx, rfl⟩
  obtain ⟨U, hU, hxU, hUO⟩ :=
    TopologicalSpace.Opens.isBasis_iff_nbhd.mp Y.isBasis_affineOpens hxO
  refine ⟨r ⁻¹ᵁ U, ⟨U, hU, rfl⟩, hxU, fun y hy ↦ ?_⟩
  obtain ⟨z, hz, hzy⟩ := hUO hy
  rwa [hr.injective hzy] at hz

variable {U : Y.Opens} (hU : IsAffineOpen U)

/-- **Local essential surjectivity of base change.** The affine model of a weakly étale
`Γ(X, r ⁻¹ᵁ U)`-algebra `B` is covered by a single morphism from the base change of the affine
model of an ind-étale `Γ(Y, U)`-algebra. -/
lemma exists_overPullback_cover (B : Type u) [CommRing B] [Algebra Γ(X, r ⁻¹ᵁ U) B]
    [Algebra.WeaklyEtale Γ(X, r ⁻¹ᵁ U) B] :
    ∃ (D : Type u) (_ : CommRing D) (_ : Algebra Γ(Y, U) D) (_ : Algebra.IndEtale Γ(Y, U) D)
      (c : (MorphismProperty.Over.pullback @WeaklyEtale ⊤ r).obj (ofAlgebra hU D) ⟶
        ofAlgebra (hU.preimage r) B),
      Sieve.generate (Presieve.singleton c) ∈ topology X _ := by
  let : Algebra Γ(Y, U) Γ(X, r ⁻¹ᵁ U) := (r.app U).hom.toAlgebra
  have hr : algebraMap Γ(Y, U) Γ(X, r ⁻¹ᵁ U) = (r.app U).hom := rfl
  have := Algebra.IsUniversalHomeomorphism.of_isUniversalHomeomorphism_app r hU
    (hU.preimage r) hr
  obtain ⟨D, _, _, hD, φ, hφ⟩ :=
    Algebra.WeaklyEtale.exists_indEtale_baseChange Γ(Y, U) Γ(X, r ⁻¹ᵁ U) B
  let e := overPullbackObjOfAlgebraIso r hU (hU.preimage r) hr D
  refine ⟨D, inferInstance, inferInstance, hD, e.hom ≫ ofAlgebraMap (hU.preimage r) φ, ?_⟩
  refine (topology X).superset_covering ?_
    (generate_singleton_ofAlgebraMap_mem_topology (hU.preimage r) φ hφ)
  rw [Sieve.generate_le_iff]
  rintro _ _ ⟨⟩
  exact ⟨_, e.inv, _, Presieve.singleton.mk, by simp⟩

/-- Base change along a universal homeomorphism is cover dense for the pro-étale topologies:
every weakly étale `X`-scheme is covered by base changes of weakly étale `Y`-schemes. -/
instance isCoverDense_overPullback :
    (MorphismProperty.Over.pullback @WeaklyEtale ⊤ r).IsCoverDense (topology X) where
  is_cover V := by
    refine mem_topology_of_ofAlgebra (isBasis_preimageAffineOpens r)
      (isAffineOpen_of_mem_preimageAffineOpens r) (O := ⊤) (by simp) _ ?_
    rintro _ ⟨U, hU, rfl⟩ - B _ _ _ f -
    obtain ⟨D, _, _, _, c, hc⟩ := exists_overPullback_cover r hU B
    refine (topology X).superset_covering ?_ hc
    rw [Sieve.generate_le_iff]
    rintro _ _ ⟨⟩
    exact Presieve.in_coverByImage _ (c ≫ f)

section LocallyFull

omit [IsUniversalHomeomorphism r] in
/-- The sieve on `W : S.ProEt` of the morphisms factoring through the affine model of an
ind-étale algebra over an affine open of `S`. -/
def indEtaleModelSieve {S : Scheme.{u}} (W : S.ProEt) : Sieve W where
  arrows Z s := ∃ (U : S.Opens) (hU : IsAffineOpen U) (T : Type u) (_ : CommRing T)
    (_ : Algebra Γ(S, U) T) (_ : Algebra.IndEtale Γ(S, U) T)
    (a : Z ⟶ ofAlgebra hU T) (m : ofAlgebra hU T ⟶ W), s = a ≫ m
  downward_closed := fun {_ _ _} ⟨U, hU, T, i₁, i₂, i₃, a, m, h'⟩ g ↦
    ⟨U, hU, T, i₁, i₂, i₃, g ≫ a, m, by rw [h', Category.assoc]⟩

omit [IsUniversalHomeomorphism r] in
/-- Every weakly étale `S`-scheme is covered by affine models of ind-étale algebras. -/
lemma indEtaleModelSieve_mem_topology {S : Scheme.{u}} (W : S.ProEt) :
    indEtaleModelSieve W ∈ topology S W :=
  mem_topology_of_indEtale_of_mem S.isBasis_affineOpens (fun _ h ↦ h) (O := ⊤) (by simp) _
    fun U hU _ T i₁ i₂ i₃ f ↦ ⟨U, hU, T, i₁, i₂, i₃, 𝟙 _, f, (Category.id_comp f).symm⟩

omit [IsUniversalHomeomorphism r] in
lemma range_hom_subset_of_hom {S : Scheme.{u}} {V W : S.ProEt} (f : V ⟶ W) :
    Set.range V.hom.base ⊆ Set.range W.hom.base := by
  rintro _ ⟨x, rfl⟩
  exact ⟨f.left.base x, by rw [← MorphismProperty.Over.w f]; rfl⟩

omit [IsUniversalHomeomorphism r] in
lemma range_ofAlgebra_hom_subset {S : Scheme.{u}} {U : S.Opens} (hU : IsAffineOpen U)
    (D : Type u) [CommRing D] [Algebra Γ(S, U) D] [Algebra.WeaklyEtale Γ(S, U) D] :
    Set.range (ofAlgebra hU D).hom.base ⊆ (U : Set S) := by
  rintro _ ⟨x, rfl⟩
  rw [ofAlgebra_hom, Scheme.Hom.comp_apply, ← hU.range_fromSpec]
  exact ⟨_, rfl⟩

omit [IsUniversalHomeomorphism r] in
lemma range_overPullback_obj_hom_subset (W : Y.ProEt) {O : Y.Opens}
    (h : Set.range W.hom.base ⊆ (O : Set Y)) :
    Set.range ((MorphismProperty.Over.pullback @WeaklyEtale ⊤ r).obj W).hom.base ⊆
      ((r ⁻¹ᵁ O : X.Opens) : Set X) := by
  rintro _ ⟨x, rfl⟩
  have e : (pullback.fst W.hom r ≫ W.hom).base x = (pullback.snd W.hom r ≫ r).base x :=
    congrArg (fun g : pullback W.hom r ⟶ Y ↦ g.base x) pullback.condition
  change (pullback.snd W.hom r ≫ r).base x ∈ O
  rw [← e]
  exact h ⟨_, rfl⟩

/-- The key case of local fullness: a morphism from the base change of an ind-étale affine model
is locally the base change of a morphism. -/
lemma imageSieve_mem_topology_of_indEtale (T₁ : Type u) [CommRing T₁] [Algebra Γ(Y, U) T₁]
    [Algebra.IndEtale Γ(Y, U) T₁] {W₂ : Y.ProEt}
    (φ : (MorphismProperty.Over.pullback @WeaklyEtale ⊤ r).obj (ofAlgebra hU T₁) ⟶
      (MorphismProperty.Over.pullback @WeaklyEtale ⊤ r).obj W₂) :
    (MorphismProperty.Over.pullback @WeaklyEtale ⊤ r).imageSieve φ ∈ topology Y _ := by
  refine (functorPushforward_overPullback_mem_topology_iff r _).mp ?_
  have hS₂ := indEtaleModelSieve_mem_topology W₂
  refine (topology X).transitive
    ((topology X).pullback_stable φ ((coverPreserving_overPullback r).cover_preserve hS₂)) _ ?_
  rintro V h ⟨Z, s, k, ⟨U₂, hU₂, T₂, _, _, _, a, m, hs⟩, hhk⟩
  subst hs
  set k' := k ≫ (MorphismProperty.Over.pullback @WeaklyEtale ⊤ r).map a
  have hhk' : h ≫ φ = k' ≫ (MorphismProperty.Over.pullback @WeaklyEtale ⊤ r).map m := by
    simp [k', hhk]
  -- `V` lies over `r⁻¹(U ⊓ U₂)`
  have hV : Set.range V.hom.base ⊆ ((r ⁻¹ᵁ (U ⊓ U₂) : X.Opens) : Set X) := by
    intro x hx
    refine ⟨?_, ?_⟩
    · exact range_overPullback_obj_hom_subset r _ (range_ofAlgebra_hom_subset hU T₁)
        (range_hom_subset_of_hom h hx)
    · exact range_overPullback_obj_hom_subset r _ (range_ofAlgebra_hom_subset hU₂ T₂)
        (range_hom_subset_of_hom k' hx)
  refine mem_topology_of_ofAlgebra (isBasis_preimageAffineOpens r)
    (isAffineOpen_of_mem_preimageAffineOpens r) hV _ ?_
  rintro _ ⟨U'', hU'', rfl⟩ hle B _ _ _ f -
  have hle' : U'' ≤ U ⊓ U₂ := fun y hy ↦ by
    obtain ⟨x, rfl⟩ := r.surjective y
    exact hle hy
  obtain ⟨D, _, _, _, c, hc⟩ := exists_overPullback_cover r hU'' B
  refine (topology X).superset_covering (Sieve.generate_singleton_le ?_) hc
  -- `c ≫ f ≫ h` and `c ≫ f ≫ k'` are base changes of morphisms of affine models
  obtain ⟨z, hz⟩ : ∃ z : ofAlgebra hU'' D ⟶ ofAlgebra hU T₁,
      (MorphismProperty.Over.pullback @WeaklyEtale ⊤ r).map z = c ≫ f ≫ h := by
    let _ : Algebra Γ(Y, U) D :=
      ((algebraMap Γ(Y, U'') D).comp
        (Y.presheaf.map (homOfLE (hle'.trans inf_le_left)).op).hom).toAlgebra
    have hD : algebraMap Γ(Y, U) D = (algebraMap Γ(Y, U'') D).comp
        (Y.presheaf.map (homOfLE (hle'.trans inf_le_left)).op).hom := rfl
    have := weaklyEtale_of_le hU hU'' _ D hD
    let e := ofAlgebraIsoOfLE hU hU'' (hle'.trans inf_le_left) D hD
    let _ : Algebra Γ(Y, U) Γ(X, r ⁻¹ᵁ U) := (r.app U).hom.toAlgebra
    obtain ⟨ψ, hψ⟩ := exists_overPullback_map_eq_of_indEtale r hU (hU.preimage r) rfl
      ((MorphismProperty.Over.pullback @WeaklyEtale ⊤ r).map e.hom ≫ c ≫ f ≫ h)
    refine ⟨e.inv ≫ ψ, ?_⟩
    rw [Functor.map_comp, hψ, ← Category.assoc, ← Functor.map_comp, e.inv_hom_id,
      CategoryTheory.Functor.map_id, Category.id_comp]
  obtain ⟨w, hw⟩ : ∃ w : ofAlgebra hU'' D ⟶ ofAlgebra hU₂ T₂,
      (MorphismProperty.Over.pullback @WeaklyEtale ⊤ r).map w = c ≫ f ≫ k' := by
    let _ : Algebra Γ(Y, U₂) D :=
      ((algebraMap Γ(Y, U'') D).comp
        (Y.presheaf.map (homOfLE (hle'.trans inf_le_right)).op).hom).toAlgebra
    have hD : algebraMap Γ(Y, U₂) D = (algebraMap Γ(Y, U'') D).comp
        (Y.presheaf.map (homOfLE (hle'.trans inf_le_right)).op).hom := rfl
    have := weaklyEtale_of_le hU₂ hU'' _ D hD
    let e := ofAlgebraIsoOfLE hU₂ hU'' (hle'.trans inf_le_right) D hD
    let _ : Algebra Γ(Y, U₂) Γ(X, r ⁻¹ᵁ U₂) := (r.app U₂).hom.toAlgebra
    obtain ⟨ψ, hψ⟩ := exists_overPullback_map_eq_of_indEtale r hU₂ (hU₂.preimage r) rfl
      ((MorphismProperty.Over.pullback @WeaklyEtale ⊤ r).map e.hom ≫ c ≫ f ≫ k')
    refine ⟨e.inv ≫ ψ, ?_⟩
    rw [Functor.map_comp, hψ, ← Category.assoc, ← Functor.map_comp, e.inv_hom_id,
      CategoryTheory.Functor.map_id, Category.id_comp]
  refine ⟨_, z, 𝟙 _, ⟨w ≫ m, ?_⟩, ?_⟩
  · rw [(MorphismProperty.Over.pullback @WeaklyEtale ⊤ r).map_comp, hw, hz]
    simp only [Category.assoc, hhk']
  · simp [hz]

/-- Base change along a universal homeomorphism is locally full for the pro-étale topologies. -/
instance isLocallyFull_overPullback :
    (MorphismProperty.Over.pullback @WeaklyEtale ⊤ r).IsLocallyFull (topology X) where
  functorPushforward_imageSieve_mem {W₁ W₂} φ := by
    refine (functorPushforward_overPullback_mem_topology_iff r _).mpr ?_
    refine mem_topology_of_indEtale Y.isBasis_affineOpens (fun _ h ↦ h) (O := ⊤) (by simp) _ ?_
    rintro U hU - T _ _ _ g
    refine (topology Y).superset_covering ?_
      (imageSieve_mem_topology_of_indEtale r hU T
        ((MorphismProperty.Over.pullback @WeaklyEtale ⊤ r).map g ≫ φ))
    rintro Z z ⟨ψ, hψ⟩
    exact ⟨ψ, by rw [hψ, Functor.map_comp, Category.assoc]⟩

end LocallyFull

/-- **Topological invariance of the small pro-étale site.** Base change along a universal
homeomorphism exhibits the small pro-étale site of `Y` as a dense subsite of the small
pro-étale site of `X`. -/
lemma isDenseSubsite_overPullback :
    (MorphismProperty.Over.pullback @WeaklyEtale ⊤ r).IsDenseSubsite (topology Y)
      (topology X) where
  isCoverDense' := isCoverDense_overPullback r
  isLocallyFull' := isLocallyFull_overPullback r
  isLocallyFaithful' := isLocallyFaithful_overPullback r
  functorPushforward_mem_iff := functorPushforward_overPullback_mem_topology_iff r _

end AlgebraicGeometry.Scheme.ProEt
