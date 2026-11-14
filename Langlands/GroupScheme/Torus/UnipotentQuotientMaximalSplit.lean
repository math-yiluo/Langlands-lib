import Langlands.GroupScheme.Torus.UnipotentQuotientMaximal

/-! # Maximal split tori and split rank through unipotent quotients -/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry

namespace Langlands.GroupScheme

section Transport

variable {k : Type u} [Field k]
  {G : GroupScheme (Spec (CommRingCat.of k))}
  {T T' : CommGroupScheme (Spec (CommRingCat.of k))}

/-- Replacing the source by an isomorphic torus preserves split maximality. -/
theorem IsMaximalSplitTorus.iso_comp (e : T'.toGrp ≅ T.toGrp)
    {i : T.toGrp ⟶ G} (hi : IsMaximalSplitTorus i) :
    IsMaximalSplitTorus (e.hom ≫ i) := by
  refine ⟨⟨IsSplitTorus.of_iso e hi.1.1, hi.1.2.iso_comp e⟩, ?_⟩
  intro T'' i' hi' f hf
  have heq : (e.inv ≫ f) ≫ i' = i := by
    simpa only [Category.assoc, Iso.inv_hom_id_assoc] using
      congrArg (fun a => e.inv ≫ a) hf
  have : IsIso (e.inv ≫ f) := hi.2 T'' i' hi' (e.inv ≫ f) heq
  have : IsIso (e.hom ≫ (e.inv ≫ f)) := inferInstance
  simpa only [Iso.hom_inv_id_assoc] using this

/-- Split maximality is invariant under source isomorphisms. -/
theorem IsMaximalSplitTorus.iso_comp_iff (e : T'.toGrp ≅ T.toGrp) (i : T.toGrp ⟶ G) :
    IsMaximalSplitTorus (e.hom ≫ i) ↔ IsMaximalSplitTorus i := by
  constructor
  · intro hi
    simpa only [Iso.symm_hom, Iso.inv_hom_id_assoc] using hi.iso_comp e.symm
  · exact fun hi => hi.iso_comp e

/-- Rational subgroup conjugacy preserves maximal split tori. -/
theorem SubgroupConjugate.isMaximalSplitTorus_iff
    {i : T.toGrp ⟶ G} {i' : T'.toGrp ⟶ G} (h : SubgroupConjugate i i') :
    IsMaximalSplitTorus i ↔ IsMaximalSplitTorus i' := by
  obtain ⟨g, e, he⟩ := h
  calc
    IsMaximalSplitTorus i ↔ IsMaximalSplitTorus (i ≫ (G.innerIso g).hom) :=
      (IsMaximalSplitTorus.comp_iso_iff i (G.innerIso g)).symm
    _ ↔ IsMaximalSplitTorus (e.hom ≫ i') := by rw [he]
    _ ↔ IsMaximalSplitTorus i' := IsMaximalSplitTorus.iso_comp_iff e i'

end Transport

section GeneralPreservation

variable {k : Type u} [Field k]
  {G Q : GroupScheme (Spec (CommRingCat.of k))}
  [IsAffineHom G.X.hom] [LocallyOfFiniteType G.X.hom] [IsAffineHom Q.X.hom]
  {T : CommGroupScheme (Spec (CommRingCat.of k))}
  {i : T.toGrp ⟶ G} (hi : IsMaximalSplitTorus i) (q : G ⟶ Q)
  (hclosed : IsClosedSubgroup (i ≫ q))
  (hlift : ∀ (T' : CommGroupScheme (Spec (CommRingCat.of k)))
    (i' : T'.toGrp ⟶ Q), IsSplitSubtorus i' →
      ∃ j : T'.toGrp ⟶ G, j ≫ q = i')
  (hcompare : ∀ j : T.toGrp ⟶ G, i ≫ q = j ≫ q → SubgroupConjugate i j)

include hi hclosed hlift hcompare in
/-- Closed split-torus lifts and equal-map conjugacy imply preservation of
maximal split tori, without replacing the original source. -/
theorem IsMaximalSplitTorus.comp_of_split_torus_lifts :
    IsMaximalSplitTorus (i ≫ q) := by
  refine ⟨⟨hi.1.1, hclosed⟩, ?_⟩
  intro T' i' hi' f hf
  obtain ⟨j, hjq⟩ := hlift T' i' hi'
  have : IsClosedImmersion i'.hom.hom.left := hi'.2
  have : Mono i'.hom.hom := Over.mono_of_mono_left _
  have : Mono j.hom.hom :=
    mono_of_mono_fac (congrArg (fun a => a.hom.hom) hjq)
  have : IsAffineHom T'.toGrp.X.hom := by
    rw [← Over.w i'.hom.hom]
    infer_instance
  have hj : IsClosedSubgroup j := hi'.1.isTorus.isClosedSubgroup_of_mono j
  have heq : i ≫ q = (f ≫ j) ≫ q := by
    rw [Category.assoc, hjq, hf]
  have hfj : IsMaximalSplitTorus (f ≫ j) :=
    (hcompare (f ≫ j) heq).isMaximalSplitTorus_iff.mp hi
  exact hfj.2 T' j ⟨hi'.1, hj⟩ f rfl

end GeneralPreservation

section Reflection

variable {k : Type u} [Field k]
  {N G Q : GroupScheme (Spec (CommRingCat.of k))}
  [IsAffineHom N.X.hom] [LocallyOfFiniteType N.X.hom]
  [IsAffineHom G.X.hom] [LocallyOfFiniteType G.X.hom]
  [IsAffineHom Q.X.hom] [LocallyOfFiniteType Q.X.hom]
  (n : N ⟶ G) (hN : IsUnipotent N) (q : G ⟶ Q)
  (hker : SubgroupFunctor.range (kernelι q) ≤ SubgroupFunctor.range n)

include hN hker

omit [LocallyOfFiniteType G.X.hom] in
/-- Split subtori remain closed split subtori if the full kernel is contained
in a represented affine unipotent subgroup. -/
theorem IsSplitSubtorus.comp_of_unipotent_kernel
    {T : CommGroupScheme (Spec (CommRingCat.of k))}
    {i : T.toGrp ⟶ G} (hi : IsSplitSubtorus i) : IsSplitSubtorus (i ≫ q) :=
  ⟨hi.1, hN.closed_torus_quotient unipotentClosedSubgroup hi.1.isTorus n i hi.2 q hker⟩

/-- Maximality in the quotient implies maximality upstairs. This direction
does not require a perfect field or a split unipotent kernel. -/
theorem IsMaximalSplitTorus.of_comp_of_unipotent_kernel
    {T : CommGroupScheme (Spec (CommRingCat.of k))}
    {i : T.toGrp ⟶ G} (hi : IsMaximalSplitTorus (i ≫ q)) :
    IsMaximalSplitTorus i := by
  have : IsClosedImmersion (i ≫ q).hom.hom.left := hi.1.2
  have : Mono (i ≫ q).hom.hom := Over.mono_of_mono_left _
  have : Mono i.hom.hom :=
    mono_of_mono_fac (show i.hom.hom ≫ q.hom.hom = (i ≫ q).hom.hom from rfl)
  have : IsAffineHom T.toGrp.X.hom := by
    rw [← Over.w (i ≫ q).hom.hom]
    infer_instance
  refine ⟨⟨hi.1.1, hi.1.1.isTorus.isClosedSubgroup_of_mono i⟩, ?_⟩
  intro T' i' hi' f hf
  apply hi.2 T' (i' ≫ q) (hi'.comp_of_unipotent_kernel n hN q hker) f
  simpa only [Category.assoc] using congrArg (fun a => a ≫ q) hf

end Reflection

section Quotient

variable {k : Type u} [Field k]
  {N G Q : GroupScheme (Spec (CommRingCat.of k))}
  [IsAffineHom G.X.hom] [LocallyOfFiniteType G.X.hom]
  [IsAffineHom Q.X.hom] [LocallyOfFiniteType Q.X.hom]
  [Smooth N.X.hom] [ConnectedSpace N.X.left]
  (n : N ⟶ G) (hn : IsClosedSubgroup n) (hN : IsUnipotent N)
  (q : G ⟶ Q) (hq : RelativeRoot.IsFppfQuotient (SubgroupFunctor.range n) q)

include hn hN hq

/-- A smooth connected split-unipotent quotient preserves maximal split tori. -/
theorem IsMaximalSplitTorus.comp_of_split_unipotent_kernel
    {T : CommGroupScheme (Spec (CommRingCat.of k))}
    {i : T.toGrp ⟶ G} (hi : IsMaximalSplitTorus i)
    (hNsplit : RelativeRoot.IsSplitUnipotent N) : IsMaximalSplitTorus (i ≫ q) := by
  let : IsClosedImmersion n.hom.hom.left := hn
  let : Mono n.hom.hom := Over.mono_of_mono_left _
  let : IsAffineHom N.X.hom := HomogeneousQuotient.affine_subgroup_of_closed G N n hn
  have hc : IsClosedSubgroup (i ≫ q) :=
    hN.closed_torus_quotient unipotentClosedSubgroup hi.1.1.isTorus n i hi.1.2 q hq.2.2.2.le
  apply hi.comp_of_split_torus_lifts q hc
  · intro T' i' hi'
    exact hi'.1.isTorus.exists_splitUnipotentQuotientLift n q hq hN hNsplit
      RelativeRoot.splitUnipotentStableVectorSubgroup
      RelativeRoot.torusVectorActionLinearization i' hi'.2
  · intro j hj
    exact subgroupConjugate_of_isTorus_fppf_split_unipotent_kernel_of_structuralStatements
      RelativeRoot.splitUnipotentStableVectorSubgroup
      RelativeRoot.torusVectorActionLinearization splitUnipotentAffineTorsorStatement
      n hn inferInstance inferInstance hN hNsplit q hq i j hj hi.1.1.isTorus

/-- A prescribed quotient maximal split torus lifts with exactly its original
source, and every such lift is maximal. -/
theorem IsMaximalSplitTorus.exists_splitUnipotentQuotientLift
    {T : CommGroupScheme (Spec (CommRingCat.of k))}
    {j : T.toGrp ⟶ Q} (hj : IsMaximalSplitTorus j)
    (hNsplit : RelativeRoot.IsSplitUnipotent N) :
    ∃ i : T.toGrp ⟶ G, i ≫ q = j ∧ IsMaximalSplitTorus i := by
  let : IsClosedImmersion n.hom.hom.left := hn
  let : Mono n.hom.hom := Over.mono_of_mono_left _
  let : IsAffineHom N.X.hom := HomogeneousQuotient.affine_subgroup_of_closed G N n hn
  obtain ⟨i, hi⟩ := hj.1.1.isTorus.exists_splitUnipotentQuotientLift n q hq hN hNsplit
    RelativeRoot.splitUnipotentStableVectorSubgroup
    RelativeRoot.torusVectorActionLinearization j hj.1.2
  refine ⟨i, hi, ?_⟩
  apply IsMaximalSplitTorus.of_comp_of_unipotent_kernel n hN q hq.2.2.2.le
  simpa only [hi] using hj

/-- Split rank is unchanged by a smooth connected split-unipotent quotient. -/
theorem splitRank_eq_of_split_unipotent_quotient
    (hNsplit : RelativeRoot.IsSplitUnipotent N) : splitRank G = splitRank Q := by
  let : IsClosedImmersion n.hom.hom.left := hn
  let : Mono n.hom.hom := Over.mono_of_mono_left _
  let : IsAffineHom N.X.hom := HomogeneousQuotient.affine_subgroup_of_closed G N n hn
  apply le_antisymm
  · refine iSup_le fun I => iSup_le fun _ => iSup_le fun i => iSup_le fun hi => ?_
    exact card_le_splitRank I (i ≫ q)
      (hN.closed_torus_quotient unipotentClosedSubgroup
        (isSplitTorus_splitTorus I).isTorus n i hi q hq.2.2.2.le)
  · refine iSup_le fun I => iSup_le fun _ => iSup_le fun j => iSup_le fun hj => ?_
    have hT := (isSplitTorus_splitTorus (S := Spec (CommRingCat.of k)) I).isTorus
    obtain ⟨i, hi⟩ := hT.exists_splitUnipotentQuotientLift n q hq hN hNsplit
      RelativeRoot.splitUnipotentStableVectorSubgroup
      RelativeRoot.torusVectorActionLinearization j hj
    have : IsClosedImmersion j.hom.hom.left := hj
    have : Mono j.hom.hom := Over.mono_of_mono_left _
    have : Mono i.hom.hom := mono_of_mono_fac (congrArg (fun a => a.hom.hom) hi)
    have : IsAffineHom (splitTorus (Spec (CommRingCat.of k)) I).X.hom := by
      rw [← Over.w j.hom.hom]
      infer_instance
    exact card_le_splitRank I i (hT.isClosedSubgroup_of_mono i)

/-- Over a perfect field, maximal split tori are preserved and reflected by
the represented smooth connected unipotent quotient. -/
theorem IsMaximalSplitTorus.comp_iff_of_perfect_field_unipotent_kernel [PerfectField k]
    {T : CommGroupScheme (Spec (CommRingCat.of k))} (i : T.toGrp ⟶ G) :
    IsMaximalSplitTorus (i ≫ q) ↔ IsMaximalSplitTorus i := by
  let : IsClosedImmersion n.hom.hom.left := hn
  let : IsAffineHom N.X.hom := HomogeneousQuotient.affine_subgroup_of_closed G N n hn
  constructor
  · exact fun hi => hi.of_comp_of_unipotent_kernel n hN q hq.2.2.2.le
  · exact fun hi => hi.comp_of_split_unipotent_kernel n hn hN q hq
      (perfectFieldUnipotentSplit k N inferInstance hN)

/-- A prescribed maximal split torus in the quotient lifts over a perfect field. -/
theorem IsMaximalSplitTorus.exists_perfectFieldUnipotentQuotientLift [PerfectField k]
    {T : CommGroupScheme (Spec (CommRingCat.of k))}
    {j : T.toGrp ⟶ Q} (hj : IsMaximalSplitTorus j) :
    ∃ i : T.toGrp ⟶ G, i ≫ q = j ∧ IsMaximalSplitTorus i := by
  let : IsClosedImmersion n.hom.hom.left := hn
  let : IsAffineHom N.X.hom := HomogeneousQuotient.affine_subgroup_of_closed G N n hn
  exact hj.exists_splitUnipotentQuotientLift n hn hN q hq
    (perfectFieldUnipotentSplit k N inferInstance hN)

/-- Perfect-field smooth connected unipotent quotients preserve split rank. -/
theorem splitRank_eq_of_perfect_field_unipotent_quotient [PerfectField k] :
    splitRank G = splitRank Q := by
  let : IsClosedImmersion n.hom.hom.left := hn
  let : IsAffineHom N.X.hom := HomogeneousQuotient.affine_subgroup_of_closed G N n hn
  exact splitRank_eq_of_split_unipotent_quotient n hn hN q hq
    (perfectFieldUnipotentSplit k N inferInstance hN)

end Quotient

/-- Exact maximal-split-torus transfer, prescribed-source lifting and split-rank
equality for represented unipotent quotients over perfect fields. -/
def PerfectFieldUnipotentQuotientMaximalSplitTorusStatement : Prop :=
  ∀ (k : Type u) [Field k] [PerfectField k]
    (N G Q : GroupScheme (Spec (CommRingCat.of k)))
    [IsAffineHom G.X.hom] [LocallyOfFiniteType G.X.hom]
    [IsAffineHom Q.X.hom] [LocallyOfFiniteType Q.X.hom]
    [Smooth N.X.hom] [ConnectedSpace N.X.left]
    (n : N ⟶ G) (q : G ⟶ Q),
    IsClosedSubgroup n → IsUnipotent N →
    RelativeRoot.IsFppfQuotient (SubgroupFunctor.range n) q →
    (∀ (T : CommGroupScheme (Spec (CommRingCat.of k))) (i : T.toGrp ⟶ G),
      IsMaximalSplitTorus (i ≫ q) ↔ IsMaximalSplitTorus i) ∧
    (∀ (T : CommGroupScheme (Spec (CommRingCat.of k))) (j : T.toGrp ⟶ Q),
      IsMaximalSplitTorus j →
      ∃ i : T.toGrp ⟶ G, i ≫ q = j ∧ IsMaximalSplitTorus i) ∧
    splitRank G = splitRank Q

theorem perfectFieldUnipotentQuotientMaximalSplitTorus :
    PerfectFieldUnipotentQuotientMaximalSplitTorusStatement.{u} := by
  intro k _ _ N G Q _ _ _ _ _ _ n q hn hN hq
  exact ⟨fun T i => IsMaximalSplitTorus.comp_iff_of_perfect_field_unipotent_kernel n hn hN q hq i,
    fun T j hj => hj.exists_perfectFieldUnipotentQuotientLift n hn hN q hq,
    splitRank_eq_of_perfect_field_unipotent_quotient n hn hN q hq⟩

end Langlands.GroupScheme
