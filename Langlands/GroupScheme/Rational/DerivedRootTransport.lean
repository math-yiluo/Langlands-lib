import Langlands.GroupScheme.Rational.CentralIsogenyRootTransport
import Langlands.GroupScheme.Rational.CharacterFpqcProof
import Langlands.GroupScheme.Rational.CentralRootRestriction
import Langlands.GroupScheme.Rational.SplitTorusFactorization
import Langlands.GroupScheme.Derived.DynamicRootContainment

/-! # Actual root subgroup transport through a derived inclusion -/

noncomputable section

set_option backward.isDefEq.respectTransparency false

universe u

open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory
open CategoryTheory.CartesianMonoidalCategory AlgebraicGeometry
open scoped CategoryTheory.MonObj

namespace Langlands.GroupScheme.RelativeRoot

private abbrev flatSurjectiveProperty : MorphismProperty Scheme.{u} :=
  @Flat ⊓ @Surjective

private abbrev fpqcProperty : MorphismProperty Scheme.{u} :=
  @QuasiCompact ⊓ (@Flat ⊓ @Surjective)

set_option backward.isDefEq.respectTransparency false in
private theorem epi_whiskerLeft {B : Scheme.{u}} {X Y : Over B} (f : X ⟶ Y)
    [Flat f.left] [Surjective f.left] (U : Over B) : Epi (U ◁ f) := by
  have hp : flatSurjectiveProperty (U ◁ f).left :=
    MorphismProperty.pullbackMap (P := flatSurjectiveProperty)
      (by change flatSurjectiveProperty (𝟙 U.left); exact ⟨inferInstance, inferInstance⟩)
      ⟨inferInstance, inferInstance⟩ (by simp) (Over.w f).symm
  obtain ⟨hf, hs⟩ := hp
  let : Flat (U ◁ f).left := hf
  let : Surjective (U ◁ f).left := hs
  have : Epi (U ◁ f).left := Flat.epi_of_flat_of_surjective _
  exact Over.epi_of_epi_left _

set_option backward.isDefEq.respectTransparency false in
private theorem effectiveEpi_whiskerLeft {B : Scheme.{u}} {X Y : Over B} (f : X ⟶ Y)
    [QuasiCompact f.left] [Flat f.left] [Surjective f.left] (U : Over B) :
    EffectiveEpi (U ◁ f).left := by
  have hp : fpqcProperty (U ◁ f).left :=
    MorphismProperty.pullbackMap (P := fpqcProperty)
      (by change fpqcProperty (𝟙 U.left); exact ⟨inferInstance, inferInstance, inferInstance⟩)
      ⟨inferInstance, inferInstance, inferInstance⟩ (by simp) (Over.w f).symm
  obtain ⟨hq, hf, hs⟩ := hp
  let : QuasiCompact (U ◁ f).left := hq
  let : Flat (U ◁ f).left := hf
  let : Surjective (U ◁ f).left := hs
  infer_instance

section ClosedEmbedding

variable {B : Scheme.{u}} {S : CommGroupScheme B} {D G : GroupScheme B}
    (j : S.toGrp ⟶ D) (a : characterLattice S) (d : D ⟶ G)
    [QuasiCompact (CommGroupScheme.groupHom a).hom.hom.left]
    [Flat (CommGroupScheme.groupHom a).hom.hom.left]
    [Surjective (CommGroupScheme.groupHom a).hom.hom.left]

/-- An fpqc character lets a full torus orbit extension lift through a closed
ambient subgroup, including on nonreduced test schemes. -/
theorem IsOrbitExtension.exists_of_closedEmbedding (hd : IsClosedSubgroup d)
    {U : Over B} {g : U ⟶ D.X} {v : U ⊗ AffineLine.scheme B ⟶ G.X}
    (hv : IsOrbitExtension (j ≫ d) a (g ≫ d.hom.hom) v) :
    ∃ v', IsOrbitExtension j a g v' ∧ v' ≫ d.hom.hom = v := by
  have : IsClosedImmersion d.hom.hom.left := hd
  have : Mono d.hom.hom := Over.mono_of_mono_left _
  have : EffectiveEpi (U ◁ (CommGroupScheme.groupHom a).hom.hom).left :=
    effectiveEpi_whiskerLeft _ U
  have hsq : CommSq (orbit j g).left
      (U ◁ (CommGroupScheme.groupHom a).hom.hom).left d.hom.hom.left
      (U ◁ AffineLine.unitInclusion B ≫ v).left := by
    have he : orbit j g ≫ d.hom.hom =
        U ◁ (CommGroupScheme.groupHom a).hom.hom ≫
          (U ◁ AffineLine.unitInclusion B ≫ v) := by
      rw [← orbit_comp_hom]
      rw [IsOrbitExtension, whiskerLeft_comp, Category.assoc] at hv
      exact hv.symm
    exact ⟨congrArg Over.Hom.left he⟩
  let k : U ⊗ (Gm B).X ⟶ D.X := Over.homMk hsq.lift (by
    rw [← Over.w d.hom.hom, ← Category.assoc, hsq.fac_right, Over.w])
  have hk : k ≫ d.hom.hom = U ◁ AffineLine.unitInclusion B ≫ v :=
    Over.OverMorphism.ext hsq.fac_right
  obtain ⟨v', hv'⟩ := AffineLine.exists_lift_of_unitInclusion d.hom.hom v k hk
  refine ⟨v', ?_, hv'⟩
  rw [IsOrbitExtension, ← cancel_mono d.hom.hom, Category.assoc, hv',
    ← orbit_comp_hom]
  exact hv

/-- With an fpqc character, taking the preimage under a closed ambient
embedding gives exactly the source root subgroup functor. -/
theorem subgroup_comap_closedEmbedding (hd : IsClosedSubgroup d) :
    (subgroup (j ≫ d) a).comap d = subgroup j a := by
  have : IsClosedImmersion d.hom.hom.left := hd
  have : Mono d.hom.hom := Over.mono_of_mono_left _
  ext U g
  rw [SubgroupFunctor.mem_comap]
  constructor
  · rintro ⟨v, hv, hv0⟩
    obtain ⟨v', hv', he⟩ := hv.exists_of_closedEmbedding j a d hd
    refine ⟨v', hv', ?_⟩
    apply (cancel_mono d.hom.hom).mp
    rw [← Dynamic.evalZero_comp, he, hv0, MonObj.one_comp]
  · exact comp_mem_subgroup j a d

end ClosedEmbedding

section CentralComplement

variable {B : Scheme.{u}} {T A S : CommGroupScheme B} {G : GroupScheme B}
    (e : T ⟶ S) (c : A ⟶ S) (i : S.toGrp ⟶ G) (a : characterLattice S)

/-- The actual product map of the retained torus and its commutative complement. -/
abbrev centralComplementProduct : T.toGrp ⊗ A.toGrp ⟶ S.toGrp :=
  prodHom (CommGroupScheme.groupHom e)
  (CommGroupScheme.groupHom c) (fun _ _ _ => Commute.all _ _)

private theorem centralComplement_character (hz : c ≫ a = 0)
    {V : Over B} (x : V ⟶ (T.toGrp ⊗ A.toGrp).X) :
    x ≫ (centralComplementProduct e c).hom.hom ≫ (CommGroupScheme.groupHom a).hom.hom =
      x ≫ fst T.X A.X ≫ (CommGroupScheme.groupHom (e ≫ a)).hom.hom := by
  rw [← Category.assoc, comp_prodHom, MonObj.mul_comp]
  change (x ≫ fst T.X A.X ≫ (CommGroupScheme.groupHom (e ≫ a)).hom.hom) *
    (x ≫ snd T.X A.X ≫ (CommGroupScheme.groupHom (c ≫ a)).hom.hom) = _
  rw [hz]
  change _ * ((x ≫ snd T.X A.X) ≫ (1 : A.X ⟶ (Gm B).X)) = _
  rw [MonObj.comp_one, mul_one]

private theorem centralComplement_conjugation
    (hc : IsCentral (CommGroupScheme.groupHom c ≫ i))
    {V : Over B} (x : V ⟶ (T.toGrp ⊗ A.toGrp).X) (g : V ⟶ G.X) :
    (x ≫ (centralComplementProduct e c).hom.hom ≫ i.hom.hom) * g *
        (x ≫ (centralComplementProduct e c).hom.hom ≫ i.hom.hom)⁻¹ =
      (x ≫ fst T.X A.X ≫ (CommGroupScheme.groupHom e ≫ i).hom.hom) * g *
        (x ≫ fst T.X A.X ≫ (CommGroupScheme.groupHom e ≫ i).hom.hom)⁻¹ := by
  rw [← Category.assoc x (centralComplementProduct e c).hom.hom,
    comp_prodHom, MonObj.mul_comp]
  let b := (productPointsEquiv T.toGrp A.toGrp V x).2 ≫
    (CommGroupScheme.groupHom c ≫ i).hom.hom
  have hb : Commute b g := commute_of_mem_center (hc V _) g
  change (_ * b) * g * (_ * b)⁻¹ = _
  rw [mul_inv_rev]
  simp only [mul_assoc]
  rw [← mul_assoc b g, hb.eq]
  simp only [mul_assoc, mul_inv_cancel_left]
  rfl

variable [hpflat : Flat (centralComplementProduct e c).hom.hom.left]
    [hpsurj : Surjective (centralComplementProduct e c).hom.hom.left]

include hpflat hpsurj

/-- A flat surjective product with a central complement detects nonzero
characters vanishing on the complement. -/
theorem precomp_ne_zero_of_centralComplement (hz : c ≫ a = 0) (ha : a ≠ 0) :
    e ≫ a ≠ 0 := by
  intro he
  apply ha
  have : Epi (centralComplementProduct e c).hom.hom.left :=
    Flat.epi_of_flat_of_surjective _
  have : Epi (centralComplementProduct e c).hom.hom := Over.epi_of_epi_left _
  apply Additive.toMul.injective
  apply Grp.hom_ext
  apply (cancel_epi (centralComplementProduct e c).hom.hom).mp
  have h := centralComplement_character e c a hz (𝟙 _)
  rw [Category.id_comp, he] at h
  change (centralComplementProduct e c).hom.hom ≫
    (CommGroupScheme.groupHom a).hom.hom =
      (centralComplementProduct e c).hom.hom ≫ (1 : S.X ⟶ (Gm B).X)
  change _ = fst T.X A.X ≫ (1 : T.X ⟶ (Gm B).X) at h
  simpa only [MonObj.comp_one] using h

/-- A central complement in a flat surjective product preserves and reflects
the actual full-torus extension through a character trivial on the complement. -/
theorem isOrbitExtension_centralComplement_iff
    (hc : IsCentral (CommGroupScheme.groupHom c ≫ i)) (hz : c ≫ a = 0)
    {U : Over B} {g : U ⟶ G.X} {v : U ⊗ AffineLine.scheme B ⟶ G.X} :
    IsOrbitExtension (CommGroupScheme.groupHom e ≫ i) (e ≫ a) g v ↔
      IsOrbitExtension i a g v := by
  constructor
  · intro hv
    have : Epi (U ◁ (centralComplementProduct e c).hom.hom) :=
      epi_whiskerLeft _ U
    rw [IsOrbitExtension]
    apply (cancel_epi (U ◁ (centralComplementProduct e c).hom.hom)).mp
    have hchar : (U ◁ (centralComplementProduct e c).hom.hom) ≫
        U ◁ ((CommGroupScheme.groupHom a).hom.hom ≫ AffineLine.unitInclusion B) =
        (U ◁ fst T.X A.X) ≫
          U ◁ ((CommGroupScheme.groupHom (e ≫ a)).hom.hom ≫
            AffineLine.unitInclusion B) := by
      rw [← whiskerLeft_comp, ← whiskerLeft_comp]
      congr 1
      have he := centralComplement_character e c a hz (𝟙 _)
      simp only [Category.id_comp] at he
      rw [← Category.assoc, he, Category.assoc]
    have horbit : (U ◁ (centralComplementProduct e c).hom.hom) ≫ orbit i g =
        (U ◁ fst T.X A.X) ≫ orbit (CommGroupScheme.groupHom e ≫ i) g := by
      simp only [orbit, AutomorphicAction.conjugation_act, MonObj.comp_mul,
        GrpObj.comp_inv, whiskerLeft_snd_assoc, whiskerLeft_fst_assoc]
      exact centralComplement_conjugation e c i hc (snd U _) (fst U _ ≫ g)
    rw [IsOrbitExtension] at hv
    rw [← Category.assoc, hchar, Category.assoc, hv, horbit]
  · exact fun hv => hv.precomp_torus_hom i a e

/-- The all-test root subgroup is unchanged by discarding a central complement
whose product with the retained torus is flat and surjective. -/
theorem subgroup_centralComplement
    (hc : IsCentral (CommGroupScheme.groupHom c ≫ i)) (hz : c ≫ a = 0) :
    subgroup (CommGroupScheme.groupHom e ≫ i) (e ≫ a) = subgroup i a := by
  ext U g
  constructor
  · rintro ⟨v, hv, hv0⟩
    exact ⟨v, (isOrbitExtension_centralComplement_iff e c i a hc hz).mp hv, hv0⟩
  · exact mem_subgroup_precomp_torus_hom i a e

end CentralComplement

section Derived

variable {k : Type u} [Field k]
    {T A S : CommGroupScheme (Spec (CommRingCat.of k))}
    {D G : GroupScheme (Spec (CommRingCat.of k))}
    (e : T ⟶ S) (c : A ⟶ S) (j : T.toGrp ⟶ D) (i : S.toGrp ⟶ G)
    (d : D ⟶ G) (hd : IsDerivedSubgroup d)
    (h : j ≫ d = CommGroupScheme.groupHom e ≫ i)
    (hT : IsSplitTorus T.toGrp)
    [Flat (centralComplementProduct e c).hom.hom.left]
    [Surjective (centralComplementProduct e c).hom.hom.left]
    (hc : IsCentral (CommGroupScheme.groupHom c ≫ i))
    (a : characterLattice S) (hz : c ≫ a = 0) (ha : a ≠ 0)

include hd h hT hc hz ha

/-- The actual derived inclusion reflects the root subgroup after restricting
the torus and discarding a supplied flat-surjective central complement. -/
theorem subgroup_comap_derived :
    (subgroup i a).comap d = subgroup j (e ≫ a) := by
  obtain ⟨hq, hf, hs⟩ := characterFpqc k T hT (e ≫ a)
    (precomp_ne_zero_of_centralComplement e c a hz ha)
  let : QuasiCompact (CommGroupScheme.groupHom (e ≫ a)).hom.hom.left := hq
  let : Flat (CommGroupScheme.groupHom (e ≫ a)).hom.hom.left := hf
  let : Surjective (CommGroupScheme.groupHom (e ≫ a)).hom.hom.left := hs
  rw [← subgroup_centralComplement e c i a hc hz, ← h]
  exact subgroup_comap_closedEmbedding j (e ≫ a) d hd.1

variable (hS : IsSplitTorus S.toGrp)

include hS

/-- For a nonzero character, the actual derived inclusion has exactly the
ambient root subgroup as its all-test image. -/
theorem subgroup_map_derived :
    (subgroup j (e ≫ a)).map d = subgroup i a := by
  rw [← subgroup_comap_derived e c j i d hd h hT hc a hz ha,
    SubgroupFunctor.map_comap]
  have hle : subgroup i a ≤ SubgroupFunctor.range d := by
    rw [hd.2]
    exact subgroup_le_derivedSubgroup i hS ha
  ext U g
  exact ⟨fun hg => hg.2, fun hg => ⟨hle U hg, hg⟩⟩

/-- Actual root points in the derived group and ambient group are identified
by the derived inclusion, on every test scheme. -/
def derivedRootPointsEquiv (U : Over (Spec (CommRingCat.of k))) :
    (subgroup j (e ≫ a)).carrier U ≃* (subgroup i a).carrier U := by
  have hm := subgroup_map_derived e c j i d hd h hT hc a hz ha hS
  have : Mono d.hom.hom := hd.isRepresentedBy.1
  let f : (subgroup j (e ≫ a)).carrier U →* (subgroup i a).carrier U :=
    { toFun := fun x => ⟨x.val ≫ d.hom.hom, by
        rw [← hm]
        exact SubgroupFunctor.mem_map.mpr ⟨x.val, x.property, rfl⟩⟩
      map_one' := Subtype.ext (MonObj.one_comp _)
      map_mul' := fun x y => Subtype.ext (MonObj.mul_comp _ _ _) }
  refine MulEquiv.ofBijective f ⟨?_, ?_⟩
  · intro x y he
    apply Subtype.ext
    exact (cancel_mono d.hom.hom).mp (congrArg Subtype.val he)
  · intro y
    have hy : y.val ∈ ((subgroup j (e ≫ a)).map d).carrier U := by
      rw [hm]
      exact y.property
    obtain ⟨x, hx, hxy⟩ := SubgroupFunctor.mem_map.mp hy
    exact ⟨⟨x, hx⟩, Subtype.ext hxy⟩

@[simp] theorem derivedRootPointsEquiv_coe
    (U : Over (Spec (CommRingCat.of k)))
    (x : (subgroup j (e ≫ a)).carrier U) :
    (derivedRootPointsEquiv e c j i d hd h hT hc a hz ha hS U x : U ⟶ G.X) =
      x.val ≫ d.hom.hom := rfl

end Derived

section ActualRoots

variable {k : Type u} [Field k]
    {T A S : CommGroupScheme (Spec (CommRingCat.of k))}
    {D G : GroupScheme (Spec (CommRingCat.of k))}
    [IsAffineHom G.X.hom] [LocallyOfFiniteType G.X.hom]
    (e : T ⟶ S) (c : A ⟶ S) (j : T.toGrp ⟶ D) (i : S.toGrp ⟶ G)
    (d : D ⟶ G) (hd : IsDerivedSubgroup d)
    (h : j ≫ d = CommGroupScheme.groupHom e ≫ i)
    (hT : IsSplitTorus T.toGrp) (hS : IsSplitTorus S.toGrp)
    (hA : IsSplitTorus A.toGrp)
    [Flat (centralComplementProduct e c).hom.hom.left]
    [Surjective (centralComplementProduct e c).hom.hom.left]
    (hc : IsCentral (CommGroupScheme.groupHom c ≫ i))
    (a : characterLattice S) (ha : a ∈ relativeRoots i)

include hd h hT hS hA hc ha

/-- For an actual ambient root, centrality supplies the vanishing on the
complement, so the derived-root comparison has no separate vanishing premise. -/
def derivedRelativeRootPointsEquiv (U : Over (Spec (CommRingCat.of k))) :
    (subgroup j (e ≫ a)).carrier U ≃* (subgroup i a).carrier U :=
  derivedRootPointsEquiv e c j i d hd h hT hc a
    (root_restrict_eq_zero_of_isCentral i c hA hc ha)
    (mem_relativeRoots.mp ha).1 hS U

@[simp] theorem derivedRelativeRootPointsEquiv_coe
    (U : Over (Spec (CommRingCat.of k)))
    (x : (subgroup j (e ≫ a)).carrier U) :
    (derivedRelativeRootPointsEquiv e c j i d hd h hT hS hA hc a ha U x : U ⟶ G.X) =
      x.val ≫ d.hom.hom := rfl

end ActualRoots

end Langlands.GroupScheme.RelativeRoot
