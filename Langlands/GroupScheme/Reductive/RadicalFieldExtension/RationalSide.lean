import Langlands.GroupScheme.Reductive.RadicalFieldExtension.RationalSideInterface
import Langlands.GroupScheme.IdentityComponentAction
import Langlands.GroupScheme.NormalizedSubgroup
import Langlands.GroupScheme.Absolute.FiniteIndexQuotientProperProof

/-! # The rational-side contradiction

Over an algebraically closed field `k`, let `Γ` be a normal solvable group of rational points of a
smooth affine group `G` acting unipotently in a closed embedding into `GL_N`, and suppose all
rational zeros of a prime `𝔭` strictly inside the augmentation ideal lie in `Γ`. The identity
component of the closure of `Γ` is then a nontrivial smooth connected normal unipotent closed
subgroup, so `G` does not have trivial unipotent radical. -/

noncomputable section

universe u

open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory
  CategoryTheory.CartesianMonoidalCategory AlgebraicGeometry
open scoped CategoryTheory.MonObj

namespace Langlands.GroupScheme.RadicalFieldExtension

open RationalZariski

/-- Over a field, a nilpotent square matrix vanishes at the power given by its size. -/
theorem pow_card_eq_zero_of_isNilpotent {K : Type*} [Field K] {N : Type} [Fintype N]
    [DecidableEq N] {A : Matrix N N K} (hA : IsNilpotent A) : A ^ Fintype.card N = 0 := by
  have h := (Matrix.isNilpotent_charpoly_sub_pow_of_isNilpotent hA).eq_zero
  rw [sub_eq_zero] at h
  have := Matrix.aeval_self_charpoly A
  rwa [h, map_pow, Polynomial.aeval_X] at this

section Closure

variable {k : Type u} [Field k] {G : GroupScheme (Spec (CommRingCat.of k))}

/-- A global function vanishing at every rational point of `S` vanishes at every rational point
located in the closure of the locations of `S`. -/
theorem evaluation_eq_zero_of_mem_rationalPointClosure
    {S : Set (Over.mk (𝟙 (Spec (CommRingCat.of k))) ⟶ G.X)} (s : Γ(G.X.left, ⊤))
    (hS : ∀ c ∈ S, evaluation G c s = 0)
    {x : Over.mk (𝟙 (Spec (CommRingCat.of k))) ⟶ G.X} (hx : x ∈ rationalPointClosure G S) :
    evaluation G x s = 0 := by
  let _ := topology G
  have hind : Topology.IsInducing (location G) := Topology.IsInducing.induced _
  have hx' : x ∈ closure S := by
    rw [hind.closure_eq_preimage_closure_image]
    exact hx
  exact closure_minimal hS (isClosed_evaluation_eq_zero s) hx'

/-- Unipotence of a group of rational points in a matrix representation extends to the rational
points in the closure of its locations. -/
theorem isNilpotent_of_mem_pointClosureSubgroup {N : Type} [Fintype N] [DecidableEq N]
    (ρ : MatrixRepresentation G N) (Γ : Subgroup (Over.mk (𝟙 (Spec (CommRingCat.of k))) ⟶ G.X))
    (hΓ : ∀ g ∈ Γ, IsNilpotent ((ρ.rationalMatrix g : Matrix N N k) - 1))
    {x : Over.mk (𝟙 (Spec (CommRingCat.of k))) ⟶ G.X} (hx : x ∈ pointClosureSubgroup G Γ) :
    IsNilpotent ((ρ.rationalMatrix x : Matrix N N k) - 1) := by
  let M : Matrix N N Γ(G.X.left, ⊤) := fun i j =>
    ρ.hom.hom.left.appTop (GeneralLinear.entrySection N _ i j)
  have hM : ∀ y : Over.mk (𝟙 (Spec (CommRingCat.of k))) ⟶ G.X,
      (evaluation G y).mapMatrix ((M - 1) ^ Fintype.card N) =
        ((ρ.rationalMatrix y : Matrix N N k) - 1) ^ Fintype.card N := by
    intro y
    have hentry : (evaluation G y).mapMatrix M = (ρ.rationalMatrix y : Matrix N N k) := by
      ext i j
      rw [MatrixRepresentation.rationalMatrix_apply_apply]
      rfl
    rw [map_pow, map_sub, map_one, hentry]
  refine ⟨Fintype.card N, ?_⟩
  rw [← hM]
  ext a b
  refine evaluation_eq_zero_of_mem_rationalPointClosure _ (fun c hc => ?_) hx
  have h := congrArg (fun A : Matrix N N k => A a b) (hM c)
  simp only [pow_card_eq_zero_of_isNilpotent (hΓ c hc), Matrix.zero_apply] at h
  exact h

end Closure

section Factor

variable {k : Type u} [Field k] [IsAlgClosed k]

/-- A morphism from a reduced scheme locally of finite type over an algebraically closed field
factors through a closed immersion once every rational point lands in its image. -/
theorem exists_lift_of_rationalPoints {P Y X : Over (Spec (CommRingCat.of k))}
    [IsReduced P.left] [LocallyOfFiniteType P.hom] (i : Y ⟶ X) [IsClosedImmersion i.left]
    (f : P ⟶ X)
    (h : ∀ x : Over.mk (𝟙 (Spec (CommRingCat.of k))) ⟶ P,
      (x ≫ f).left (IsLocalRing.closedPoint k) ∈ Set.range i.left) :
    ∃ a : P ⟶ Y, a ≫ i = f := by
  have : JacobsonSpace P.left := LocallyOfFiniteType.jacobsonSpace P.hom
  have hcl : IsClosed (f.left ⁻¹' Set.range i.left) :=
    i.left.isClosedEmbedding.isClosed_range.preimage f.left.continuous
  have hpts : closedPoints P.left ⊆ f.left ⁻¹' Set.range i.left := by
    intro p hp
    let x : Over.mk (𝟙 (Spec (CommRingCat.of k))) ⟶ P :=
      Over.homMk (pointOfClosedPoint P.hom p hp) (pointOfClosedPoint_comp P.hom p hp)
    have hxp : x.left (IsLocalRing.closedPoint k) = p := pointOfClosedPoint_apply P.hom p hp _
    have hx := h x
    change f.left (x.left (IsLocalRing.closedPoint k)) ∈ _ at hx
    rw [hxp] at hx
    exact hx
  have hrange : Set.range f.left ⊆ Set.range i.left := by
    rintro _ ⟨w, rfl⟩
    have hall := closure_minimal hpts hcl
    rw [closure_closedPoints] at hall
    exact hall (Set.mem_univ w)
  obtain ⟨l, hl⟩ := FiniteIndexTransfer.exists_lift_of_range_subset i.left f.left hrange
  refine ⟨Over.homMk l ?_, Over.OverMorphism.ext hl⟩
  rw [← Over.w i, ← Category.assoc, hl, Over.w f]

variable {G Z : GroupScheme (Spec (CommRingCat.of k))} [Smooth G.X.hom] [Smooth Z.X.hom]

/-- The closed subgroup on the closure of the locations of a normal group of rational points of
a smooth group is normal, on every test scheme. -/
theorem isNormal_range_of_rationalPointClosure
    (Γ : Subgroup (Over.mk (𝟙 (Spec (CommRingCat.of k))) ⟶ G.X)) (hΓ : Γ.Normal)
    (ζ : Z ⟶ G) (hζ : IsClosedSubgroup ζ)
    (hZrange : Set.range ζ.hom.hom.left = closure (rationalPointImage G (Γ : Set _))) :
    (SubgroupFunctor.range ζ).IsNormal := by
  have : IsClosedImmersion ζ.hom.hom.left := hζ
  let : Smooth (G.X ⊗ Z.X).hom := by
    change Smooth (pullback.fst G.X.hom Z.X.hom ≫ G.X.hom)
    infer_instance
  let : IsReduced (G.X ⊗ Z.X).left :=
    Langlands.AlgebraicGeometry.SmoothReducedProof.isReduced_of_smooth_over_field
      k _ (G.X ⊗ Z.X).hom
  have hfac : ∃ a : G.X ⊗ Z.X ⟶ Z.X,
      a ≫ ζ.hom.hom = SubgroupFunctor.conjugationMap ζ (𝟙 G) := by
    refine exists_lift_of_rationalPoints ζ.hom.hom _ fun x => ?_
    let g : Over.mk (𝟙 (Spec (CommRingCat.of k))) ⟶ G.X := x ≫ fst G.X Z.X
    let y : Over.mk (𝟙 (Spec (CommRingCat.of k))) ⟶ G.X := (x ≫ snd G.X Z.X) ≫ ζ.hom.hom
    have hx : x ≫ SubgroupFunctor.conjugationMap ζ (𝟙 G) = g * y * g⁻¹ := by
      rw [← lift_comp_fst_snd x, SubgroupFunctor.lift_comp_conjugationMap]
      simp only [Grp.id_hom_hom, Category.comp_id, g, y]
    have hy : y ∈ pointClosureSubgroup G Γ := by
      rw [mem_pointClosureSubgroup, ← hZrange]
      exact ⟨(x ≫ snd G.X Z.X).left (IsLocalRing.closedPoint k), rfl⟩
    let φ : G.X ⟶ G.X := G.constantPoint g G.X * 𝟙 G.X * (G.constantPoint g G.X)⁻¹
    have hφ : ∀ z : Over.mk (𝟙 (Spec (CommRingCat.of k))) ⟶ G.X, z ≫ φ = g * z * g⁻¹ := by
      intro z
      simp only [φ, MonObj.comp_mul, GrpObj.comp_inv, comp_constantPoint, Category.comp_id]
    have hmem : y ≫ φ ∈ rationalPointClosure G Γ :=
      comp_mem_rationalPointClosure φ (fun s hs => by
        rw [hφ]
        exact subset_rationalPointClosure _ (hΓ.conj_mem s hs g)) hy
    rw [hφ] at hmem
    rw [hx, hZrange]
    exact hmem
  have hnorm : (SubgroupFunctor.range ζ).IsNormalizedBy (SubgroupFunctor.range (𝟙 G)) :=
    (SubgroupFunctor.isNormalizedBy_range_iff_exists_conjugationMap ζ (𝟙 G)).2 hfac
  intro T g x _ hx
  exact hnorm T g x (SubgroupFunctor.mem_range.2 ⟨g, by simp⟩) hx

variable [IsAffineHom Z.X.hom]

omit [IsAlgClosed k] [Smooth G.X.hom] in
/-- The identity component of a smooth affine normal closed subgroup is normal, on every test
scheme. -/
theorem isNormal_range_identityComponentι_comp (ζ : Z ⟶ G) (hζ : IsClosedSubgroup ζ)
    (hn : (SubgroupFunctor.range ζ).IsNormal) :
    (SubgroupFunctor.range (identityComponentι Z ≫ ζ)).IsNormal := by
  have : IsClosedImmersion ζ.hom.hom.left := hζ
  have : Mono ζ.hom.hom := Over.mono_of_mono_left _
  have hnorm : (SubgroupFunctor.range ζ).IsNormalizedBy (SubgroupFunctor.range (𝟙 G)) :=
    fun T g x _ hx => hn T g x (by trivial) hx
  let a := AutomorphicAction.ofNormalizedConjugation ζ (𝟙 G) hnorm
  intro T g x _ hx
  obtain ⟨y, rfl⟩ := SubgroupFunctor.mem_range.1 hx
  refine SubgroupFunctor.mem_range.2 ⟨a.onIdentityComponent.act g y, ?_⟩
  rw [Grp.comp_hom_hom, ← Category.assoc, AutomorphicAction.onIdentityComponent_act_comp]
  change (lift g (y ≫ (identityComponentι Z).hom.hom) ≫
    SubgroupFunctor.normalizedConjugation ζ (𝟙 G) hnorm) ≫ ζ.hom.hom = _
  rw [SubgroupFunctor.lift_comp_normalizedConjugation_comp]
  simp only [Grp.id_hom_hom, Category.comp_id, Category.assoc]

end Factor

/-- **The rational-side contradiction.** -/
theorem rationalSide : RationalSideStatement.{u} := by
  intro k _ _ G _ _ hG N _ _ ρ hρ 𝔭 h𝔭 h𝔭lt Γ hΓn hΓs hΓu hΓ
  have : IsClosedImmersion ρ.hom.hom.left := hρ
  have : IsAffine G.X.left := isAffine_of_isAffineHom G.X.hom
  -- The closure `Z` of the locations of `Γ`, and its identity component `Z⁰`.
  obtain ⟨Z, ζ, hζ, hZsm, hZrange⟩ := rationalPointClosureSubgroup k G Γ
  have : IsClosedImmersion ζ.hom.hom.left := hζ
  have : Smooth Z.X.hom := hZsm
  have : IsAffineHom Z.X.hom := by
    rw [← Over.w ζ.hom.hom]
    infer_instance
  let j := identityComponentι Z ≫ ζ
  have : IsClosedImmersion j.hom.hom.left := by
    change IsClosedImmersion ((identityComponentι Z).hom.hom.left ≫ ζ.hom.hom.left)
    infer_instance
  have hj : IsClosedSubgroup j := inferInstanceAs (IsClosedImmersion j.hom.hom.left)
  have hjmem : ∀ x : Over.mk (𝟙 (Spec (CommRingCat.of k))) ⟶ (identityComponent Z).X,
      x ≫ j.hom.hom ∈ pointClosureSubgroup G Γ := by
    intro x
    change (x ≫ j.hom.hom).left (IsLocalRing.closedPoint k) ∈
      closure (rationalPointImage G (Γ : Set _))
    rw [← hZrange]
    exact ⟨(identityComponentι Z).hom.hom.left (x.left (IsLocalRing.closedPoint k)), rfl⟩
  -- Unipotence of `Z⁰`.
  have hsolv : Group.IsSolvable
      (Over.mk (𝟙 (Spec (CommRingCat.of k))) ⟶ (identityComponent Z).X) := by
    have := isSolvable_pointClosureSubgroup (H := G) Γ
    refine Group.isSolvable_of_isSolvable_injective
      (f := (IsMonHom.monoidHom j.hom.hom _).codRestrict (pointClosureSubgroup G Γ) hjmem) ?_
    intro x y hxy
    have hxy' : x ≫ j.hom.hom = y ≫ j.hom.hom := congrArg Subtype.val hxy
    have h' : x.left ≫ j.hom.hom.left = y.left ≫ j.hom.hom.left := by
      rw [← Over.comp_left, ← Over.comp_left, hxy']
    exact Over.OverMorphism.ext ((cancel_mono j.hom.hom.left).1 h')
  have : IsClosedImmersion (ρ.restrict j).hom.hom.left := by
    change IsClosedImmersion (j.hom.hom.left ≫ ρ.hom.hom.left)
    infer_instance
  have hunip : IsUnipotent (identityComponent Z) :=
    isUnipotent_of_isNilpotent_rationalMatrix (ρ.restrict j) hsolv fun x => by
      rw [MatrixRepresentation.rationalMatrix_restrict]
      exact isNilpotent_of_mem_pointClosureSubgroup ρ Γ hΓu (hjmem x)
  -- Normality of `Z⁰`.
  have hnorm : (SubgroupFunctor.range j).IsNormal :=
    isNormal_range_identityComponentι_comp ζ hζ
      (isNormal_range_of_rationalPointClosure Γ hΓn ζ hζ hZrange)
  have hbot := hG _ j hj inferInstance inferInstance hunip hnorm
  -- The point `ξ` of `G` at which `𝔭` is the vanishing prime lies on `Z⁰`.
  let t := G.X.left.toSpecΓ
  obtain ⟨ξ, hξ⟩ := t.homeomorph.surjective ⟨𝔭, inferInstance⟩
  rw [Scheme.Hom.homeomorph_apply] at hξ
  have hspec : ∀ y, ξ ⤳ y ↔ 𝔭 ≤ (t y).asIdeal := by
    intro y
    rw [← t.homeomorph.isInducing.specializes_iff, Scheme.Hom.homeomorph_apply,
      Scheme.Hom.homeomorph_apply, hξ]
    exact (PrimeSpectrum.le_iff_specializes (⟨𝔭, inferInstance⟩ : PrimeSpectrum Γ(G.X.left, ⊤))
      (t y)).symm
  have hpt : ∀ x : Over.mk (𝟙 (Spec (CommRingCat.of k))) ⟶ G.X,
      (t (x.left (IsLocalRing.closedPoint k))).asIdeal = RingHom.ker x.left.appTop.hom :=
    fun x => BorelFieldExtension.toSpecΓ_asIdeal_of_field x.left _
  have he1 : (1 : Over.mk (𝟙 (Spec (CommRingCat.of k))) ⟶ G.X).left
      (IsLocalRing.closedPoint k) = IdentityComponent.identityPoint G := by
    rw [CategoryTheory.Hom.one_def]
    exact IdentityComponent.unit_left_apply G _
  have hte : (t (IdentityComponent.identityPoint G)).asIdeal =
      RingHom.ker (1 : Over.mk (𝟙 (Spec (CommRingCat.of k))) ⟶ G.X).left.appTop.hom := by
    rw [← he1, hpt]
  have hJ : JacobsonSpace G.X.left := LocallyOfFiniteType.jacobsonSpace G.X.hom
  have hξζ : ξ ∈ Set.range ζ.hom.hom.left := by
    have hcl : IsClosed (Set.range ζ.hom.hom.left) :=
      ζ.hom.hom.left.isClosedEmbedding.isClosed_range
    have hsub : closure {ξ} ∩ closedPoints G.X.left ⊆ Set.range ζ.hom.hom.left := by
      rintro p ⟨hp, hpc⟩
      let x : Over.mk (𝟙 (Spec (CommRingCat.of k))) ⟶ G.X :=
        Over.homMk (pointOfClosedPoint G.X.hom p hpc) (pointOfClosedPoint_comp G.X.hom p hpc)
      have hxp : x.left (IsLocalRing.closedPoint k) = p :=
        pointOfClosedPoint_apply G.X.hom p hpc _
      have hx : x ∈ Γ := hΓ x (by
        rw [← hpt x, hxp]
        exact (hspec p).1 (specializes_iff_mem_closure.2 hp))
      rw [hZrange, ← hxp]
      exact subset_closure ⟨x, hx, rfl⟩
    have h1 : closure {ξ} ⊆ Set.range ζ.hom.hom.left := by
      rw [← closure_inter_closedPoints isClosed_closure]
      exact closure_minimal hsub hcl
    exact h1 (subset_closure rfl)
  obtain ⟨ξ', rfl⟩ := hξζ
  have heZ : ζ.hom.hom.left (IdentityComponent.identityPoint Z) =
      IdentityComponent.identityPoint G := by
    simp only [IdentityComponent.identityPoint]
    rw [← Scheme.Hom.comp_apply, ← Over.comp_left, IsMonHom.one_hom]
  have hξe : ζ.hom.hom.left ξ' ⤳ IdentityComponent.identityPoint G := by
    rw [hspec, hte]
    exact h𝔭lt.le
  have hξ'e : ξ' ⤳ IdentityComponent.identityPoint Z := by
    rw [← ζ.hom.hom.left.isClosedEmbedding.isInducing.specializes_iff, heZ]
    exact hξe
  have hξ'mem : ξ' ∈ Set.range (identityComponentι Z).hom.hom.left := by
    rw [IdentityComponent.range_identityComponentι]
    exact hξ'e.mem_open (IdentityComponent.isClopen_identitySet Z).isOpen
      mem_connectedComponent
  obtain ⟨w, rfl⟩ := hξ'mem
  -- Triviality of `Z⁰` would put `ξ` at the identity, so `𝔭` would be the augmentation ideal.
  have hj1 : j.hom.hom = 1 := by
    have hmem : j.hom.hom ∈ (SubgroupFunctor.range j).carrier (identityComponent Z).X :=
      SubgroupFunctor.mem_range.2 ⟨𝟙 _, Category.id_comp _⟩
    rw [hbot, SubgroupFunctor.bot_carrier, Subgroup.mem_bot] at hmem
    exact hmem
  have hw : j.hom.hom.left w = IdentityComponent.identityPoint G := by
    rw [hj1, CategoryTheory.Hom.one_def]
    exact IdentityComponent.unit_left_apply G _
  have hw' : (t (j.hom.hom.left w)).asIdeal = 𝔭 := congrArg PrimeSpectrum.asIdeal hξ
  rw [hw, hte] at hw'
  exact h𝔭lt.ne hw'.symm

end Langlands.GroupScheme.RadicalFieldExtension
