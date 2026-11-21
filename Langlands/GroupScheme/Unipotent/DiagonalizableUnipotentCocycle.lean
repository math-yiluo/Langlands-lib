import Langlands.GroupScheme.Torus.DiagonalizableVectorOneCocycle
import Langlands.GroupScheme.Unipotent.DiagonalizableAdditiveQuotientProof
import Langlands.GroupScheme.Lie.DimensionInduction
import Langlands.GroupScheme.IdentityComponentAction
import Langlands.GroupScheme.AutomorphicAction.CocycleExactSequence
import Langlands.GroupScheme.Reductive.SemisimpleIdentityComponent.TensorCore
import Langlands.GroupScheme.UnipotentClosedSubgroupProof
import Langlands.GroupScheme.Unipotent.CharZeroConnectedProof
import Langlands.AbelianScheme.Kernel

/-! # Diagonalizable one-cocycles in smooth connected unipotent groups -/

noncomputable section
universe u
open CategoryTheory Opposite AlgebraicGeometry
open scoped CategoryTheory.MonObj
open CategoryTheory.MonoidalCategory CategoryTheory.CartesianMonoidalCategory

namespace Langlands.GroupScheme.diagonalizableUnipotentCocycle
open RelativeRoot

variable {k : Type u} [Field k]

/-- The linear coordinates of `𝔾ₐⁿ` are linear for the action through a character. -/
theorem isLinearVectorCoordinates_weightAction {S : CommGroupScheme (Spec (CommRingCat.of k))}
    (χ : characterLattice S) {n : ℕ} :
    IsLinearVectorCoordinates (VectorGroup.weightAction (n := n) χ)
      (VectorGroup.coordinates (CommRingCat.of k) n) := by
  refine ⟨VectorGroup.isNaturalVectorCoordinates, fun T h c v => ?_⟩
  rw [VectorGroup.coordinates_weightAction_act, VectorGroup.coordinates_weightAction_act,
    MulEquiv.apply_symm_apply, toAdd_ofAdd, smul_comm]

/-- The kernel of a smooth homomorphism is smooth. -/
theorem smooth_kernel {G H : GroupScheme (Spec (CommRingCat.of k))} (f : G ⟶ H)
    [Smooth f.hom.hom.left] : Smooth (kernel f).X.hom :=
  MorphismProperty.of_isPullback (kernel_isPullback_scheme f) ‹_›

/-- The kernel of a homomorphism to a separated group is affine over the base when the
source is. -/
theorem isAffineHom_kernel {G H : GroupScheme (Spec (CommRingCat.of k))} (f : G ⟶ H)
    [IsAffineHom G.X.hom] [IsSeparated H.X.hom] : IsAffineHom (kernel f).X.hom := by
  rw [← Over.w (kernelι f).hom.hom]
  infer_instance

local notation "𝔻" Λ => CommGroupScheme.toGrp (Diagonalizable.groupScheme (CommRingCat.of k) Λ)
local notation "T₀" => Over.mk (𝟙 (Spec (CommRingCat.of k)))

/-- A morphism from `T₀ × D(Λ)` to a group sending `(1, 1)` to the identity lands in the
identity component, when `D(Λ)` is connected, or when the target is unipotent and the
field is algebraically closed of characteristic zero. -/
theorem range_subset_identitySet [IsAlgClosed k] (Λ : Type u) [AddCommGroup Λ]
    (hD : ConnectedSpace (𝔻 Λ).X.left ∨ CharZero k)
    (K : GroupScheme (Spec (CommRingCat.of k))) [IsAffineHom K.X.hom]
    [LocallyOfFiniteType K.X.hom] (hK : IsUnipotent K)
    (z : (T₀) ⊗ (𝔻 Λ).X ⟶ K.X) (hz : lift (𝟙 (T₀)) (1 : (T₀) ⟶ (𝔻 Λ).X) ≫ z = 1) :
    Set.range z.left ⊆ IdentityComponent.identitySet K := by
  rcases hD with hD | hD
  · let σ : (𝔻 Λ).X ⟶ (T₀) ⊗ (𝔻 Λ).X := lift (Over.mkIdTerminal.from _) (𝟙 _)
    have hσ : snd (T₀) (𝔻 Λ).X ≫ σ = 𝟙 _ := by
      apply CartesianMonoidalCategory.hom_ext
      · rw [Category.assoc, lift_fst, Category.id_comp]
        exact Over.mkIdTerminal.hom_ext _ _
      · rw [Category.assoc, lift_snd, Category.comp_id, Category.id_comp]
    have hη : η[(𝔻 Λ).X] ≫ σ ≫ z = η[K.X] := by
      have h1 : η[(𝔻 Λ).X] ≫ σ = lift (𝟙 (T₀)) (1 : (T₀) ⟶ (𝔻 Λ).X) := by
        apply CartesianMonoidalCategory.hom_ext
        · rw [Category.assoc, lift_fst, lift_fst]
          exact Over.mkIdTerminal.hom_ext _ _
        · rw [Category.assoc, lift_snd, lift_snd, Category.comp_id, Hom.one_def,
            toUnit_unique (toUnit (T₀)) (𝟙 _), Category.id_comp]
      rw [← Category.assoc, h1, hz, Hom.one_def, toUnit_unique (toUnit (T₀)) (𝟙 _),
        Category.id_comp]
    have hsub := IdentityComponent.range_subset_identitySet K (σ ≫ z) η[(𝔻 Λ).X] hη
    rintro _ ⟨x, rfl⟩
    refine hsub ⟨(snd (T₀) (𝔻 Λ).X).left x, ?_⟩
    rw [← Scheme.Hom.comp_apply, ← Over.comp_left, ← Category.assoc, hσ, Category.id_comp]
  · have : ConnectedSpace K.X.left :=
      Unipotent.connectedSpace_of_isUnipotent_of_isAlgClosed K hK
    intro x _
    rw [IdentityComponent.identitySet, PreconnectedSpace.connectedComponent_eq_univ]
    trivial

open AutomorphicAction

/-- The kernel inclusion composed with a homomorphism is trivial. -/
theorem kernelι_comp_eq_one {G H : GroupScheme (Spec (CommRingCat.of k))} (f : G ⟶ H) :
    (kernelι f).hom.hom ≫ f.hom.hom = 1 := by
  rw [(kernel_isPullback f).w, Hom.one_def]

/-- A surjective homomorphism onto `𝔾ₐ` does not factor through a subgroup on which it
is trivial: the composite of the inclusion of the identity component of its kernel is
not an isomorphism. -/
theorem not_isIso_identityComponentι_comp_kernelι [IsAlgClosed k]
    {U : GroupScheme (Spec (CommRingCat.of k))}
    (f : U ⟶ VectorGroup.groupScheme (CommRingCat.of k) 1)
    [Surjective f.hom.hom.left] [LocallyOfFiniteType f.hom.hom.left]
    [Smooth (kernel f).X.hom] [IsAffineHom (kernel f).X.hom] :
    ¬ IsIso (identityComponentι (kernel f) ≫ kernelι f) := by
  intro hiso
  set n := identityComponentι (kernel f) ≫ kernelι f
  let w₁ : (T₀) ⟶ (VectorGroup.groupScheme (CommRingCat.of k) 1).X :=
    (VectorGroup.coordinates (CommRingCat.of k) 1 (T₀)).symm (Multiplicative.ofAdd fun _ => 1)
  obtain ⟨u, hu⟩ := SemisimpleIdentityComponent.exists_rationalPoint_lift f.hom.hom w₁
  have hinv : (inv n).hom.hom ≫ n.hom.hom = 𝟙 _ := by
    rw [← Grp.comp_hom_hom, IsIso.inv_hom_id]
    rfl
  have hu1 : u ≫ f.hom.hom = 1 := by
    rw [← Category.comp_id u, ← hinv]
    simp only [n, Grp.comp_hom_hom, Category.assoc, kernelι_comp_eq_one, MonObj.comp_one]
  rw [hu1] at hu
  have h0 := congrArg (fun x => (VectorGroup.coordinates (CommRingCat.of k) 1 (T₀) x).toAdd 0) hu
  simp only [w₁, map_one, toAdd_one, MulEquiv.apply_symm_apply, toAdd_ofAdd, Pi.zero_apply] at h0
  have h1 := congrArg (Scheme.ΓSpecIso (CommRingCat.of k)).hom.hom h0
  simp only [map_zero, map_one] at h1
  exact zero_ne_one h1

/-- The additive group is affine over the base. -/
local instance : IsAffineHom (VectorGroup.groupScheme (CommRingCat.of k) 1).X.hom := by
  change IsAffineHom (Spec.map (CommRingCat.ofHom (algebraMap k (MvPolynomial (Fin 1) k))))
  infer_instance

/-- The property proved by induction on the dimension: every rational one-cocycle of
`D(Λ)` in the unipotent group is a coboundary. -/
def CoboundaryProperty [IsAlgClosed k] (Λ : Type u) [AddCommGroup Λ]
    (U : GroupScheme (Spec (CommRingCat.of k))) : Prop :=
  IsUnipotent U → ∀ (a : AutomorphicAction (𝔻 Λ) U) (c : a.Cocycle (T₀)),
    ∃ v : (T₀) ⟶ U.X, c = a.coboundary v

/-- The induction step: split off an equivariant smooth surjection onto `𝔾ₐ`, kill the
image cocycle by the linear case, and pass to the identity component of the kernel,
which has smaller dimension. -/
theorem step [IsAlgClosed k] (Λ : Type u) [AddCommGroup Λ]
    (hD : ConnectedSpace (𝔻 Λ).X.left ∨ CharZero k)
    (U : GroupScheme (Spec (CommRingCat.of k)))
    [Smooth U.X.hom] [IsAffineHom U.X.hom] [ConnectedSpace U.X.left]
    (ih : ∀ (H : GroupScheme (Spec (CommRingCat.of k)))
      [Smooth H.X.hom] [IsAffineHom H.X.hom] [ConnectedSpace H.X.left],
      Lie.dimension H < Lie.dimension U → CoboundaryProperty Λ H) :
    CoboundaryProperty Λ U := by
  intro hU a c
  by_cases hbot : SubgroupFunctor.range (𝟙 U) = ⊥
  · have hpt : ∀ {T : Over (Spec (CommRingCat.of k))} (x : T ⟶ U.X), x = 1 := by
      intro T x
      have hx : x ∈ (SubgroupFunctor.range (𝟙 U)).carrier T :=
        SubgroupFunctor.mem_range.2 ⟨x, Category.comp_id x⟩
      rw [hbot, SubgroupFunctor.bot_carrier, Subgroup.mem_bot] at hx
      exact hx
    refine ⟨1, Cocycle.ext ?_⟩
    rw [hpt c.hom, hpt (a.coboundary 1).hom]
  obtain ⟨χ, f, hfsm, hfsurj, hfeq⟩ :=
    diagonalizableAdditiveQuotient.diagonalizableUnipotentAdditiveQuotient k Λ U ‹_› ‹_› hU hbot a
  have hf : a.IsEquivariant (VectorGroup.weightAction (n := 1) χ) f :=
    fun h x => hfeq _ h x
  obtain ⟨w, hw⟩ := diagonalizableVectorOneCocycle.exists_coboundary Λ
    (VectorGroup.weightAction (n := 1) χ) (VectorGroup.coordinates (CommRingCat.of k) 1)
    (isLinearVectorCoordinates_weightAction χ) (c.map f hf)
  obtain ⟨g, hg⟩ := SemisimpleIdentityComponent.exists_rationalPoint_lift f.hom.hom w
  set c' := Cocycle.conjugate g⁻¹ c with hc'
  have htriv : c'.map f hf = Cocycle.trivial (T₀) := by
    rw [hc', Cocycle.map_conjugate, hw, ← hg, GrpObj.inv_comp]
    exact Cocycle.conjugate_inv_conjugate (g ≫ f.hom.hom) (Cocycle.trivial (T₀))
  have hmem : c'.hom ∈ (SubgroupFunctor.range (kernelι f)).carrier ((T₀) ⊗ (𝔻 Λ).X) := by
    rw [mem_range_kernelι_iff]
    exact congrArg Cocycle.hom htriv
  obtain ⟨z, hz⟩ := SubgroupFunctor.mem_range.1 hmem
  have : Smooth (kernel f).X.hom := smooth_kernel f
  have : IsAffineHom (kernel f).X.hom := isAffineHom_kernel f
  have hKclosed : IsClosedSubgroup (kernelι f) := kernelι_isClosedImmersion f
  have hKU : IsUnipotent (kernel f) := unipotentClosedSubgroup k U (kernel f) (kernelι f)
    hKclosed hU
  have hz1 : lift (𝟙 (T₀)) (1 : (T₀) ⟶ (𝔻 Λ).X) ≫ z = 1 := by
    apply (cancel_mono (kernelι f).hom.hom).1
    rw [Category.assoc, hz, MonObj.one_comp]
    exact c'.one (𝟙 _)
  have hzK := range_subset_identitySet Λ hD (kernel f) hKU z hz1
  let y := FiniteEtaleImage.liftOver (identityComponentι (kernel f)).hom.hom z (by
    rw [IdentityComponent.range_identityComponentι]
    exact hzK)
  let n := identityComponentι (kernel f) ≫ kernelι f
  have hi : (SubgroupFunctor.range (kernelι f)).IsRepresentedBy (kernelι f) :=
    ⟨inferInstance, rfl⟩
  have hF : a.IsStable (SubgroupFunctor.range (kernelι f)) := by
    intro T h x hx
    rw [mem_range_kernelι_iff] at hx ⊢
    rw [hf h x, hx, AutomorphicAction.act_one]
  let aK := a.onRepresentedIdentityComponent (kernelι f) hi hF
  have hn : aK.IsEquivariant a n := fun h x =>
    a.onRepresentedIdentityComponent_act_comp (kernelι f) hi hF h x
  have : Mono n.hom.hom := by
    rw [Grp.comp_hom_hom]
    infer_instance
  have hc : c'.hom ∈ (SubgroupFunctor.range n).carrier ((T₀) ⊗ (𝔻 Λ).X) := by
    refine SubgroupFunctor.mem_range.2 ⟨y, ?_⟩
    rw [Grp.comp_hom_hom, ← Category.assoc, FiniteEtaleImage.liftOver_fac, hz]
  have hnclosed : IsClosedSubgroup n := by
    change IsClosedImmersion (identityComponentι (kernel f) ≫ kernelι f).hom.hom.left
    rw [Grp.comp_hom_hom, Over.comp_left]
    have : IsClosedImmersion (kernelι f).hom.hom.left := hKclosed
    infer_instance
  have hdim : Lie.dimension (identityComponent (kernel f)) < Lie.dimension U :=
    Lie.dimension_lt_of_proper_closedSubgroup n hnclosed
      (not_isIso_identityComponentι_comp_kernelι f)
  have hK0U : IsUnipotent (identityComponent (kernel f)) :=
    unipotentClosedSubgroup k U _ n hnclosed hU
  obtain ⟨v, hv⟩ := ih (identityComponent (kernel f)) hdim hK0U aK (c'.lift n hn hc)
  have hd : c' = a.coboundary (v ≫ n.hom.hom) := by
    rw [← Cocycle.map_coboundary n hn v, ← hv]
    exact (Cocycle.lift_map n hn c' hc).symm
  refine ⟨g * (v ≫ n.hom.hom), ?_⟩
  have he := congrArg (Cocycle.conjugate g) hd
  rwa [hc', Cocycle.conjugate_conjugate_inv, Cocycle.conjugate_coboundary] at he

/-- Over an algebraically closed field, when `D(Λ)` is connected or the characteristic is
zero, every rational one-cocycle of `D(Λ)` in a smooth connected affine unipotent group is
a coboundary. -/
theorem exists_coboundary [IsAlgClosed k] (Λ : Type u) [AddCommGroup Λ]
    (hD : ConnectedSpace (𝔻 Λ).X.left ∨ CharZero k)
    (U : GroupScheme (Spec (CommRingCat.of k)))
    [Smooth U.X.hom] [IsAffineHom U.X.hom] [ConnectedSpace U.X.left]
    (hU : IsUnipotent U) (a : AutomorphicAction (𝔻 Λ) U) (c : a.Cocycle (T₀)) :
    ∃ v : (T₀) ⟶ U.X, c = a.coboundary v :=
  smoothConnectedAffineGroup_lieDimension_induction (CoboundaryProperty Λ)
    (fun U _ _ _ ih => step Λ hD U ih) U hU a c

/-- The same conclusion for a smooth unipotent group that need not be connected: the
cocycle lands in the identity component, to which the action restricts. -/
theorem exists_coboundary_of_smooth [IsAlgClosed k] (Λ : Type u) [AddCommGroup Λ]
    (hD : ConnectedSpace (𝔻 Λ).X.left ∨ CharZero k)
    (U : GroupScheme (Spec (CommRingCat.of k))) [Smooth U.X.hom] [IsAffineHom U.X.hom]
    (hU : IsUnipotent U) (a : AutomorphicAction (𝔻 Λ) U) (c : a.Cocycle (T₀)) :
    ∃ v : (T₀) ⟶ U.X, c = a.coboundary v := by
  have hsub := range_subset_identitySet Λ hD U hU c.hom (c.one (𝟙 _))
  let y := FiniteEtaleImage.liftOver (identityComponentι U).hom.hom c.hom (by
    rw [IdentityComponent.range_identityComponentι]
    exact hsub)
  let n := identityComponentι U
  let aU := a.onIdentityComponent
  have hn : aU.IsEquivariant a n := fun h x => a.onIdentityComponent_act_comp h x
  have hc : c.hom ∈ (SubgroupFunctor.range n).carrier ((T₀) ⊗ (𝔻 Λ).X) :=
    SubgroupFunctor.mem_range.2 ⟨y, FiniteEtaleImage.liftOver_fac _ _ _⟩
  have hU0 : IsUnipotent (identityComponent U) :=
    unipotentClosedSubgroup k U _ n (IdentityComponent.isClosedSubgroup_identityComponentι U) hU
  obtain ⟨v, hv⟩ := exists_coboundary Λ hD (identityComponent U) hU0 aU (c.lift n hn hc)
  refine ⟨v ≫ n.hom.hom, ?_⟩
  rw [← Cocycle.map_coboundary n hn v, ← hv]
  exact (Cocycle.lift_map n hn c hc).symm

end Langlands.GroupScheme.diagonalizableUnipotentCocycle
