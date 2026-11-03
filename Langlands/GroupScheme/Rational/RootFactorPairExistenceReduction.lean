import Langlands.GroupScheme.Rational.RootFactorPairTransport
import Langlands.GroupScheme.Rational.KernelCentralizerComponentReductiveStatement
import Langlands.GroupScheme.Rational.KernelCentralizerStructureProof
import Langlands.GroupScheme.Rational.GenericCocharacter
import Langlands.GroupScheme.Rational.BruhatContractionReduction
import Langlands.GroupScheme.Dynamic.PositivePowers
import Langlands.GroupScheme.Dynamic.ActionAffineRepresentability

/-! # Opposite factor-pair existence from the existing geometric targets -/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry
open scoped CategoryTheory.MonObj

namespace Langlands.GroupScheme

namespace AutomorphicAction

section Restriction

variable {B : Scheme.{u}} {H Q K G : GroupScheme B}

/-- Successive restrictions compose the actual acting homomorphisms. -/
theorem restrict_restrict (e : AutomorphicAction Q G) (q : H ⟶ Q) (r : K ⟶ H) :
    (e.restrict q).restrict r = e.restrict (r ≫ q) := by
  apply ext_act
  intro U s x
  simp only [restrict_act, Grp.comp_hom_hom, Category.assoc]

/-- An fpqc restriction has the same all-test fixed points as the original
action, even when acting points have no global lifts. -/
theorem fixedSubgroup_restrict_of_fpqc (e : AutomorphicAction Q G) (q : H ⟶ Q)
    [QuasiCompact q.hom.hom.left] [Flat q.hom.hom.left] [Surjective q.hom.hom.left] :
    (e.restrict q).fixedSubgroup = e.fixedSubgroup := by
  apply SubgroupFunctor.ext
  intro U
  apply Subgroup.ext
  intro x
  constructor
  · intro hx V b s
    apply hom_ext_of_local_quotient_lift q s
    intro W d t hdt
    rw [e.naturality, hdt]
    simpa only [restrict_act, Category.assoc] using hx W (d ≫ b) t
  · intro hx V b s
    simpa only [restrict_act] using hx V b (s ≫ q.hom.hom)

end Restriction

section PositivePowers

variable {R : CommRingCat.{u}} {G : GroupScheme (Spec R)}
    [IsAffineHom G.X.hom]
    (e : AutomorphicAction (Gm (Spec R)).toGrp G)

/-- Positive integral powers preserve the identity-limit functor of an
arbitrary affine automorphic Gm-action. -/
theorem unipotent_restrict_positive_power {n : ℤ} (hn : 0 < n) :
    (e.restrict (CommGroupScheme.groupHom (Gm.powerHom (Spec R) n))).unipotent =
      e.unipotent := by
  let : IsAffineHom (Gm (Spec R)).X.hom := isSplitTorus_gm.isAffineHom
  let : IsAffine e.semidirectProduct.X.left :=
    isAffine_of_isAffineHom e.semidirectProduct.X.hom
  rw [e.semidirect_unipotent_eq_comap,
    Dynamic.unipotent_precomp_power e.semidirectInr hn]
  simpa only [restrict_id, Category.id_comp] using
    (e.semidirect_unipotent_eq_comap (𝟙 _)).symm

end PositivePowers

end AutomorphicAction

namespace RelativeRoot

section DescendedAction

variable {k : Type u} [Field k]
    {T : CommGroupScheme (Spec (CommRingCat.of k))}
    {H : GroupScheme (Spec (CommRingCat.of k))}
    [IsAffineHom H.X.hom]
    (i : T.toGrp ⟶ H) (hT : IsSplitTorus T.toGrp)
    (a : characterLattice T) (ha : a ≠ 0)
    (e : AutomorphicAction (Gm (Spec (CommRingCat.of k))).toGrp H)
    (he : e.restrict (CommGroupScheme.groupHom a) = AutomorphicAction.conjugation i)

include he

omit [IsAffineHom H.X.hom] in
/-- Restricting an actually descended conjugation action along a cocharacter
is its integral pairing power. -/
theorem descendedAction_restrict_pairing (ν : cocharacterLattice T) :
    e.restrict (CommGroupScheme.groupHom
        (Gm.powerHom (Spec (CommRingCat.of k)) (latticePairing T a ν))) =
      AutomorphicAction.cocharacterAction (CommGroupScheme.groupHom ν ≫ i) := by
  have hcomp : CommGroupScheme.groupHom ν ≫ CommGroupScheme.groupHom a =
      CommGroupScheme.groupHom
        (Gm.powerHom (Spec (CommRingCat.of k)) (latticePairing T a ν)) := by
    change CommGroupScheme.groupHom (ν ≫ a) = _
    congr 1
    exact eq_gmEndEquiv_zsmul k (ν ≫ a)
  rw [← hcomp, ← AutomorphicAction.restrict_restrict, he,
    AutomorphicAction.restrict_conjugation,
    AutomorphicAction.cocharacterAction_eq_conjugation]

include hT ha

/-- In a group whose torus conjugation actually descends through `a`, its
intrinsic `a` subgroup is exactly the dynamic subgroup of every positively
pairing cocharacter. -/
theorem dynamicUnipotent_eq_subgroup_of_descendedAction
    (ν : cocharacterLattice T) (hpos : 0 < latticePairing T a ν) :
    Dynamic.unipotent (CommGroupScheme.groupHom ν ≫ i) = subgroup i a := by
  obtain ⟨hqc, hflat, hsurj⟩ := characterFpqc k T hT a ha
  let : QuasiCompact (CommGroupScheme.groupHom a).hom.hom.left := hqc
  let : Flat (CommGroupScheme.groupHom a).hom.hom.left := hflat
  let : Surjective (CommGroupScheme.groupHom a).hom.hom.left := hsurj
  rw [← AutomorphicAction.cocharacterAction_unipotent,
    ← descendedAction_restrict_pairing i a e he ν,
    AutomorphicAction.unipotent_restrict_positive_power e hpos]
  exact (subgroup_eq_unipotent_of_restrict i a e he).symm

omit [IsAffineHom H.X.hom] in
/-- In the same descended setting, any nonorthogonal cocharacter has
exactly the full torus centralizer, on every test scheme. -/
theorem dynamicCentralizer_eq_torusCentralizer_of_descendedAction
    (ν : cocharacterLattice T) (hν : latticePairing T a ν ≠ 0) :
    Dynamic.centralizer (CommGroupScheme.groupHom ν ≫ i) = torusCentralizer i := by
  obtain ⟨hqc, hflat, hsurj⟩ := characterFpqc k T hT a ha
  let : QuasiCompact (CommGroupScheme.groupHom a).hom.hom.left := hqc
  let : Flat (CommGroupScheme.groupHom a).hom.hom.left := hflat
  let : Surjective (CommGroupScheme.groupHom a).hom.hom.left := hsurj
  have hp0 : Gm.powerHom (Spec (CommRingCat.of k)) (latticePairing T a ν) ≠ 0 := by
    intro h
    exact hν ((Gm.powerHom_injective k) (h.trans (map_zero _).symm))
  obtain ⟨hpqc, hpflat, hpsurj⟩ := characterFpqc k (Gm (Spec (CommRingCat.of k)))
    isSplitTorus_gm (Gm.powerHom _ (latticePairing T a ν)) hp0
  let : QuasiCompact (CommGroupScheme.groupHom
    (Gm.powerHom _ (latticePairing T a ν))).hom.hom.left := hpqc
  let : Flat (CommGroupScheme.groupHom
    (Gm.powerHom _ (latticePairing T a ν))).hom.hom.left := hpflat
  let : Surjective (CommGroupScheme.groupHom
    (Gm.powerHom _ (latticePairing T a ν))).hom.hom.left := hpsurj
  rw [← AutomorphicAction.cocharacterAction_centralizer,
    ← descendedAction_restrict_pairing i a e he ν]
  change (e.restrict (CommGroupScheme.groupHom
    (Gm.powerHom _ (latticePairing T a ν)))).fixedSubgroup = torusCentralizer i
  rw [AutomorphicAction.fixedSubgroup_restrict_of_fpqc]
  rw [← AutomorphicAction.fixedSubgroup_restrict_of_fpqc e
    (CommGroupScheme.groupHom a), he,
    AutomorphicAction.conjugation_fixedSubgroup_eq_torusCentralizer]

end DescendedAction

section KernelComponent

variable {k : Type u} [Field k]
    {T : CommGroupScheme (Spec (CommRingCat.of k))}
    {G C : GroupScheme (Spec (CommRingCat.of k))}
    [Smooth C.X.hom] [IsAffineHom C.X.hom]
    (i : T.toGrp ⟶ G) (hT : IsSplitTorus T.toGrp)
    (a : characterLattice T) (ha : a ≠ 0) (j : C ⟶ G)
    (hj : (kernelCentralizer i a).IsRepresentedBy j)

include ha

/-- The intrinsic root subgroup in the full-kernel identity component is
exactly the actual dynamic unipotent for every positively pairing cocharacter. -/
theorem kernelCentralizerIdentity_dynamicUnipotent_eq_subgroup
    (ν : cocharacterLattice T) (hpos : 0 < latticePairing T a ν) :
    Dynamic.unipotent
        (CommGroupScheme.groupHom ν ≫ kernelCentralizerIdentityTorus i hT a j hj) =
      subgroup (kernelCentralizerIdentityTorus i hT a j hj) a := by
  obtain ⟨hqc, hflat, hsurj⟩ := characterFpqc k T hT a ha
  let : QuasiCompact (CommGroupScheme.groupHom a).hom.hom.left := hqc
  let : Flat (CommGroupScheme.groupHom a).hom.hom.left := hflat
  let : Surjective (CommGroupScheme.groupHom a).hom.hom.left := hsurj
  exact dynamicUnipotent_eq_subgroup_of_descendedAction _ hT a ha
    (kernelCentralizerIdentityQuotientAction i hT a j hj)
    (kernelCentralizerIdentityQuotientAction_restrict i hT a j hj) ν hpos

/-- Every cocharacter nonorthogonal to the defining character has the full
torus centralizer in the actual full-kernel identity component. -/
theorem kernelCentralizerIdentity_dynamicCentralizer_eq_torusCentralizer
    (ν : cocharacterLattice T) (hν : latticePairing T a ν ≠ 0) :
    Dynamic.centralizer
        (CommGroupScheme.groupHom ν ≫ kernelCentralizerIdentityTorus i hT a j hj) =
      torusCentralizer (kernelCentralizerIdentityTorus i hT a j hj) := by
  obtain ⟨hqc, hflat, hsurj⟩ := characterFpqc k T hT a ha
  let : QuasiCompact (CommGroupScheme.groupHom a).hom.hom.left := hqc
  let : Flat (CommGroupScheme.groupHom a).hom.hom.left := hflat
  let : Surjective (CommGroupScheme.groupHom a).hom.hom.left := hsurj
  exact dynamicCentralizer_eq_torusCentralizer_of_descendedAction _ hT a ha
    (kernelCentralizerIdentityQuotientAction i hT a j hj)
    (kernelCentralizerIdentityQuotientAction_restrict i hT a j hj) ν hν

end KernelComponent

section GenericSign

variable {k : Type u} [Field k]
    {T : CommGroupScheme (Spec (CommRingCat.of k))}
    {H : GroupScheme (Spec (CommRingCat.of k))}
    [IsAffineHom H.X.hom] [LocallyOfFiniteType H.X.hom]

/-- A generic integral cocharacter can be required to pair positively with
any specified nonzero character, without a root-system premise. -/
theorem exists_genericCocharacter_pairing_pos (i : T.toGrp ⟶ H)
    (hT : IsSplitTorus T.toGrp) {a : characterLattice T} (ha : a ≠ 0) :
    ∃ ν : cocharacterLattice T,
      IsGenericCocharacter i ν ∧ 0 < latticePairing T a ν := by
  obtain ⟨ν, hν⟩ := hT.exists_pairings_ne_zero (insert a (relativeRoots i))
    ((hT.finite_relativeRoots i).insert a) (by
      intro b hb
      rcases Set.mem_insert_iff.mp hb with rfl | hb
      · exact ha
      · exact hb.1)
  have haν := hν a (Set.mem_insert a _)
  rcases lt_or_gt_of_ne haν with hneg | hpos
  · refine ⟨-ν, ?_, ?_⟩
    · intro b hb
      simpa only [map_neg, neg_ne_zero] using hν b (Set.mem_insert_of_mem a hb)
    · simpa only [map_neg] using neg_pos.mpr hneg
  · exact ⟨ν, fun b hb => hν b (Set.mem_insert_of_mem a hb), hpos⟩

end GenericSign

/-- The existing rational Bruhat and full-kernel component-reductivity
targets suffice for actual opposite-factor-pair existence. These two
geometric propositions remain explicit inputs. -/
theorem exists_oppositeFactorPair_of_bruhat_and_componentReductivity
    (hBr : RationalBruhatStatement.{u})
    (hRed : KernelCentralizerComponentReductiveStatement.{u})
    (k : Type u) [Field k] (G : GroupScheme (Spec (CommRingCat.of k)))
    (hG : IsConnectedReductive G) (T : CommGroupScheme (Spec (CommRingCat.of k)))
    (i : T.toGrp ⟶ G) (hi : IsMaximalSplitTorus i)
    (a : characterLattice T) (ha : a ≠ 0) (x : rationalPoints G)
    (hx : x ∈ (subgroup i a).carrier (Over.mk (𝟙 _))) :
    ∃ p, IsOppositeFactorPair i a x p := by
  let : IsAffineHom G.X.hom := hG.isAffineHom
  let : Smooth G.X.hom := hG.smooth
  by_cases hx1 : x = 1
  · subst x
    refine ⟨(1, 1), Subgroup.one_mem _, Subgroup.one_mem _, ?_⟩
    simpa only [one_mul] using (normalizerPoints i).one_mem
  obtain ⟨C, j, hj, hjc, hCs, _⟩ :=
    kernelCentralizerStructure k G inferInstance inferInstance T hi.1.1 i a ha
  let : Smooth C.X.hom := hCs
  let : IsClosedImmersion j.hom.hom.left := hjc
  let : IsAffineHom C.X.hom := by
    rw [← j.hom.hom.w]
    infer_instance
  let iC := kernelCentralizerIdentityTorus i hi.1.1 a j hj
  have hiC : IsMaximalSplitTorus iC := hi.kernelCentralizerIdentityTorus a j hj hjc
  have hC : IsConnectedReductive (identityComponent C) :=
    hRed k G hG T hi.1.1 i a ha C j hj hjc hCs
  let : IsAffineHom (identityComponent C).X.hom := hC.isAffineHom
  let : IsAffine (identityComponent C).X.left :=
    isAffine_of_isAffineHom (identityComponent C).X.hom
  let : Smooth (identityComponent C).X.hom := hC.smooth
  have hneg : (kernelCentralizer i (-a)).IsRepresentedBy j := by
    simpa only [kernelCentralizer_neg] using hj
  obtain ⟨ν, hν, hpos⟩ :=
    exists_genericCocharacter_pairing_pos iC hi.1.1 (neg_ne_zero.mpr ha)
  have hU : Dynamic.unipotent (CommGroupScheme.groupHom ν ≫ iC) =
      subgroup iC (-a) := by
    have h := kernelCentralizerIdentity_dynamicUnipotent_eq_subgroup
      i hi.1.1 (-a) (neg_ne_zero.mpr ha) j hneg ν hpos
    simpa only [kernelCentralizerIdentityTorus_neg i hi.1.1 a j hj] using h
  have hZ : Dynamic.centralizer (CommGroupScheme.groupHom ν ≫ iC) =
      torusCentralizer iC := by
    have h := kernelCentralizerIdentity_dynamicCentralizer_eq_torusCentralizer
      i hi.1.1 (-a) (neg_ne_zero.mpr ha) j hneg ν hpos.ne'
    simpa only [kernelCentralizerIdentityTorus_neg i hi.1.1 a j hj] using h
  have hcover := unipotentNormalizerCovering_of_parabolicNormalizerCovering iC ν hZ
    (hBr k (identityComponent C) hC T iC hiC ν hν).1
  apply (forall_exists_oppositeFactorPair_kernelCentralizerIdentity_iff
    i hi.1.1 a ha j hj hjc).mp ?_ x hx hx1
  intro y _hy _hy1
  obtain ⟨n, u, v, heq⟩ := hcover y
  have hu : (u : rationalPoints (identityComponent C)) ∈
      (subgroup iC (-a)).carrier (Over.mk (𝟙 _)) := hU ▸ u.property
  have hv : (v : rationalPoints (identityComponent C)) ∈
      (subgroup iC (-a)).carrier (Over.mk (𝟙 _)) := hU ▸ v.property
  refine ⟨((u : rationalPoints (identityComponent C))⁻¹,
    (v : rationalPoints (identityComponent C))⁻¹),
    Subgroup.inv_mem _ hu, Subgroup.inv_mem _ hv, ?_⟩
  have hn : (u : rationalPoints (identityComponent C))⁻¹ * y *
      (v : rationalPoints (identityComponent C))⁻¹ = n.val := by
    rw [heq]
    simp [mul_assoc]
  rw [hn]
  exact n.property

/-- The actual ordered pair selected from this reduction, with the two
unproved geometric targets retained as explicit inputs. -/
def oppositeFactorPairOfBruhatAndComponentReductivity
    (hBr : RationalBruhatStatement.{u})
    (hRed : KernelCentralizerComponentReductiveStatement.{u})
    (k : Type u) [Field k] (G : GroupScheme (Spec (CommRingCat.of k)))
    (hG : IsConnectedReductive G) (T : CommGroupScheme (Spec (CommRingCat.of k)))
    (i : T.toGrp ⟶ G) (hi : IsMaximalSplitTorus i)
    (a : characterLattice T) (ha : a ≠ 0) (x : rationalPoints G)
    (hx : x ∈ (subgroup i a).carrier (Over.mk (𝟙 _))) :
    {p // IsOppositeFactorPair i a x p} :=
  ⟨Classical.choose
    (exists_oppositeFactorPair_of_bruhat_and_componentReductivity
      hBr hRed k G hG T i hi a ha x hx),
    Classical.choose_spec
      (exists_oppositeFactorPair_of_bruhat_and_componentReductivity
        hBr hRed k G hG T i hi a ha x hx)⟩

end RelativeRoot

end Langlands.GroupScheme
