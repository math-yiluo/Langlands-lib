import Langlands.GroupScheme.NormalQuotientEtaleGluing
import Langlands.GroupScheme.Reductive.BaseChange
import Langlands.GroupScheme.Reductive.GenericFiberGeometry
import Langlands.GroupScheme.Rational.FppfQuotientSmooth
import Langlands.AlgebraicGeometry.SmoothEtaleSourceDescentProof

/-! # Reductivity of descended normal quotients -/

noncomputable section

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true
set_option maxHeartbeats 800000

namespace Langlands.GroupScheme

/-- Reductivity is invariant under isomorphisms over an arbitrary base. -/
theorem IsReductive.of_iso {S : Scheme.{u}} {G H : GroupScheme S}
    (e : G ≅ H) (hH : IsReductive H) : IsReductive G := by
  have hw : G.X.hom = e.hom.hom.hom.left ≫ H.X.hom :=
    (Over.w e.hom.hom.hom).symm
  have := isIso_left_of_iso e
  have := hH.smooth
  have := hH.isAffineHom
  refine ⟨?_, ?_, fun s => ?_⟩
  · rw [hw]
    infer_instance
  · rw [hw]
    infer_instance
  · exact (hH.geometricFiber s).of_iso ((GroupScheme.baseChange (geometricPoint S s)).mapIso e)

/-- For a smooth affine group, reductivity can be tested after base changes
whose images jointly contain every point of the base. -/
theorem IsReductive.of_pointwise_baseChange
    {S : Scheme.{u}} {G : GroupScheme S}
    [Smooth G.X.hom] [IsAffineHom G.X.hom]
    (hlocal : ∀ s : S, ∃ (T : Scheme.{u}) (b : T ⟶ S),
      s ∈ Set.range b ∧ IsReductive ((GroupScheme.baseChange b).obj G)) :
    IsReductive G := by
  refine ⟨inferInstance, inferInstance, fun s => ?_⟩
  obtain ⟨T, b, ⟨t, ht⟩, hT⟩ := hlocal s
  let c := T.fromSpecResidueField t ≫ b
  have hc : c (IsLocalRing.closedPoint (T.residueField t)) = s := by
    change b (T.fromSpecResidueField t _) = s
    rw [Scheme.fromSpecResidueField_apply, ht]
  have hfield : IsConnectedReductive ((GroupScheme.baseChange c).obj G) :=
    (hT.isConnectedReductive_residueFiber t).of_iso
      (baseChangeCompIso b (T.fromSpecResidueField t) G)
  let : Algebra (S.residueField (c (IsLocalRing.closedPoint (T.residueField t))))
      (T.residueField t) := (fieldPointResidueMap c).hom.toAlgebra
  have hres : IsConnectedReductive
      ((GroupScheme.baseChange (S.fromSpecResidueField
        (c (IsLocalRing.closedPoint (T.residueField t))))).obj G) :=
    IsConnectedReductive.of_fieldExtension
      (k := S.residueField (c (IsLocalRing.closedPoint (T.residueField t))))
      (K := T.residueField t)
      (hfield.of_iso (fieldPointFiberIso G c).symm)
  rw [hc] at hres
  have hgeo := connectedReductiveFieldExtensionStatement
    (S.residueField s) (AlgebraicClosure (S.residueField s)) _ hres
  exact (hgeo.of_iso
    (baseChangeCompIso (S.fromSpecResidueField s) (toAlgebraicClosure _) G)).isPseudoReductive

namespace RelativeRoot.IsFppfQuotient

/-- A supplied affine fppf quotient of a smooth affine group by a smooth
monomorphic subgroup is smooth over the base. -/
theorem smooth_target_of_smooth_represented_kernel {S : Scheme.{u}} {G N Q : GroupScheme S}
    [Smooth G.X.hom] [IsAffineHom G.X.hom] [IsAffineHom Q.X.hom]
    {i : N ⟶ G} [Mono i.hom.hom] {q : G ⟶ Q}
    (hq : RelativeRoot.IsFppfQuotient (SubgroupFunctor.range i) q)
    (hN : Smooth N.X.hom) : Smooth Q.X.hom := by
  have : QuasiCompact (q.hom.hom.left ≫ Q.X.hom) := by
    rw [Over.w q.hom.hom]
    infer_instance
  have : QuasiCompact q.hom.hom.left := QuasiCompact.of_comp _ Q.X.hom
  have : Smooth q.hom.hom.left := hq.smooth_of_smooth_kernel ⟨inferInstance, rfl⟩ hN
  have := hq.2.1
  have : Smooth (q.hom.hom.left ≫ Q.X.hom) := by
    rw [Over.w q.hom.hom]
    infer_instance
  exact Langlands.AlgebraicGeometry.smooth_of_smooth_of_surjective_of_smooth_comp
    q.hom.hom.left Q.X.hom

end RelativeRoot.IsFppfQuotient

namespace NormalQuotient

/-- A supplied affine quotient is reductive when its kernel has reductive
quotients after pointwise base changes covering the base. -/
theorem isReductive_of_pointwise_quotients
    {S : Scheme.{u}} {G N M : GroupScheme S}
    [Smooth G.X.hom] [IsAffineHom G.X.hom] [IsAffineHom M.X.hom]
    (i : N ⟶ G) [Mono i.hom.hom] (hN : Smooth N.X.hom)
    (r : G ⟶ M) (hr : RelativeRoot.IsFppfQuotient (SubgroupFunctor.range i) r)
    (hlocal : ∀ s : S, ∃ (T : Scheme.{u}) (b : T ⟶ S)
      (Q : GroupScheme T) (q : (GroupScheme.baseChange b).obj G ⟶ Q),
      s ∈ Set.range b ∧ IsReductive Q ∧
        RelativeRoot.IsFppfQuotient (SubgroupFunctor.range ((GroupScheme.baseChange b).map i)) q) :
    IsReductive M := by
  have : Smooth M.X.hom := hr.smooth_target_of_smooth_represented_kernel hN
  apply IsReductive.of_pointwise_baseChange
  intro s
  obtain ⟨T, b, Q, q, hs, hQ, hq⟩ := hlocal s
  have : IsAffineHom ((GroupScheme.baseChange b).obj G).X.hom :=
    MorphismProperty.pullback_snd G.X.hom b inferInstance
  have : IsAffineHom ((GroupScheme.baseChange b).obj M).X.hom :=
    MorphismProperty.pullback_snd M.X.hom b inferInstance
  have := hQ.isAffineHom
  have hqc : QuasiCompact (q.hom.hom.left ≫ Q.X.hom) := by
    rw [Over.w q.hom.hom]
    infer_instance
  have : QuasiCompact q.hom.hom.left := QuasiCompact.of_comp _ Q.X.hom
  let r' := (GroupScheme.baseChange b).map r
  have hqc' : QuasiCompact (r'.hom.hom.left ≫ ((GroupScheme.baseChange b).obj M).X.hom) := by
    rw [Over.w r'.hom.hom]
    infer_instance
  have : QuasiCompact r'.hom.hom.left := QuasiCompact.of_comp _ ((GroupScheme.baseChange b).obj M).X.hom
  have hr' : RelativeRoot.IsFppfQuotient
      (SubgroupFunctor.range ((GroupScheme.baseChange b).map i)) r' := by
    simpa only [SubgroupFunctor.range_baseChangeHom] using hr.baseChange b
  exact ⟨T, b, hs, hQ.of_iso (FppfQuotientComparison.iso hr' hq)⟩

/-- Reductive fppf quotients supplied on pointwise etale neighbourhoods
descend to a reductive fppf quotient over the whole base. -/
theorem exists_reductive_fppfQuotient_of_pointwise_etale
    {S : Scheme.{u}} {G N : GroupScheme S}
    [Smooth G.X.hom] [IsAffineHom G.X.hom]
    (i : N ⟶ G) [Mono i.hom.hom] (hN : Smooth N.X.hom)
    (hn : (SubgroupFunctor.range i).IsNormal)
    (hlocal : ∀ s : S, ∃ (T : Scheme.{u}) (b : T ⟶ S)
      (Q : GroupScheme T) (q : (GroupScheme.baseChange b).obj G ⟶ Q),
      Etale b ∧ s ∈ Set.range b ∧ IsReductive Q ∧
        RelativeRoot.IsFppfQuotient (SubgroupFunctor.range ((GroupScheme.baseChange b).map i)) q) :
    ∃ (M : GroupScheme S) (r : G ⟶ M), IsReductive M ∧
      RelativeRoot.IsFppfQuotient (SubgroupFunctor.range i) r := by
  have haffine : ∀ s : S, ∃ (T : Scheme.{u}) (b : T ⟶ S)
      (Q : GroupScheme T) (q : (GroupScheme.baseChange b).obj G ⟶ Q),
      Etale b ∧ s ∈ Set.range b ∧ IsAffineHom Q.X.hom ∧
        RelativeRoot.IsFppfQuotient (SubgroupFunctor.range ((GroupScheme.baseChange b).map i)) q := by
    intro s
    obtain ⟨T, b, Q, q, hb, hs, hQ, hq⟩ := hlocal s
    exact ⟨T, b, Q, q, hb, hs, hQ.isAffineHom, hq⟩
  obtain ⟨M, r, hM, hr⟩ := exists_affine_fppfQuotient_of_pointwise_etale i hN hn haffine
  let := hM
  refine ⟨M, r, isReductive_of_pointwise_quotients i hN r hr ?_, hr⟩
  intro s
  obtain ⟨T, b, Q, q, _, hs, hQ, hq⟩ := hlocal s
  exact ⟨T, b, Q, q, hs, hQ, hq⟩

end NormalQuotient

/-- Pointwise etale-local reductive quotients of a smooth affine group by a
smooth monomorphic normal subgroup descend over every scheme. -/
def ReductiveNormalQuotientEtaleGluingStatement : Prop :=
  ∀ (S : Scheme.{u}) (G N : GroupScheme S)
    [Smooth G.X.hom] [IsAffineHom G.X.hom]
    (i : N ⟶ G) [Mono i.hom.hom],
    Smooth N.X.hom → (SubgroupFunctor.range i).IsNormal →
    (∀ s : S, ∃ (T : Scheme.{u}) (b : T ⟶ S)
      (Q : GroupScheme T) (q : (GroupScheme.baseChange b).obj G ⟶ Q),
      Etale b ∧ s ∈ Set.range b ∧ IsReductive Q ∧
        RelativeRoot.IsFppfQuotient (SubgroupFunctor.range ((GroupScheme.baseChange b).map i)) q) →
    ∃ (M : GroupScheme S) (r : G ⟶ M), IsReductive M ∧
      RelativeRoot.IsFppfQuotient (SubgroupFunctor.range i) r

/-- Reductive normal quotients glue from the supplied local quotients. -/
theorem reductiveNormalQuotientEtaleGluing : ReductiveNormalQuotientEtaleGluingStatement.{u} := by
  intro S G N _ _ i _ hN hn hlocal
  exact NormalQuotient.exists_reductive_fppfQuotient_of_pointwise_etale i hN hn hlocal

end Langlands.GroupScheme
