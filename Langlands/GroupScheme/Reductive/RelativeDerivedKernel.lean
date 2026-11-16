import Langlands.GroupScheme.Reductive.RelativeDerivedInputs
import Langlands.GroupScheme.Torus.RelativeReductive
import Langlands.GroupScheme.Rational.FppfQuotientSmooth

/-! # Relative derived groups as kernels of smooth torus quotients -/

noncomputable section
universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open scoped CategoryTheory.MonObj

set_option backward.isDefEq.respectTransparency.types false

namespace Langlands.GroupScheme
namespace RelativeDerived

variable {S : Scheme.{u}} {D G Q : GroupScheme S}

/-- A smooth surjective torus quotient with semisimple full geometric kernels. -/
def IsSemisimpleTorusQuotient (q : G ⟶ Q) : Prop :=
  RelativeTorus.IsTorus Q ∧ Smooth q.hom.hom.left ∧ Surjective q.hom.hom.left ∧
    ∀ s : S, IsSemisimple (kernel ((baseChange (geometricPoint S s)).map q))

/-- The full kernel of a smooth semisimple torus quotient is admissible. -/
theorem isAdmissible_kernelι (hG : IsReductive G) {q : G ⟶ Q}
    (hq : IsSemisimpleTorusQuotient q) : IsAdmissible (kernelι q) := by
  let : IsAffineHom G.X.hom := hG.isAffineHom
  let : IsAffineHom Q.X.hom := hq.1.isAffineHom
  let : Smooth q.hom.hom.left := hq.2.1
  let : Surjective q.hom.hom.left := hq.2.2.1
  have hclosed : IsClosedSubgroup (kernelι q) := kernelι_isClosedImmersion q
  let : IsClosedImmersion (kernelι q).hom.hom.left := hclosed
  have hsmooth : Smooth (kernel q).X.hom :=
    MorphismProperty.of_isPullback (kernel_isPullback_scheme q) hq.2.1
  have haffine : IsAffineHom (kernel q).X.hom := by
    rw [← Over.w (kernelι q).hom.hom]
    infer_instance
  have hss (s : S) : IsSemisimple (geometricFiber (kernel q) s) :=
    (hq.2.2.2 s).of_iso (kernelBaseChangeIso (geometricPoint S s) q)
  refine ⟨hclosed, ?_, ⟨hsmooth, haffine, fun s =>
    (hss s).isConnectedReductive.isPseudoReductive⟩, hss, Q, q, hq.1,
    inferInstance, inferInstance, inferInstance, rfl⟩
  intro T g x _ hx
  rw [mem_range_kernelι_iff] at hx ⊢
  rw [MonObj.mul_comp, MonObj.mul_comp, GrpObj.inv_comp, hx, mul_one, mul_inv_cancel]

/-- Every specified torus quotient by an admissible subgroup is smooth. -/
theorem IsAdmissible.smooth_quotient (hG : IsReductive G) {d : D ⟶ G}
    (hd : IsAdmissible d) {q : G ⟶ Q} (hQ : RelativeTorus.IsTorus Q)
    (hq : RelativeRoot.IsFppfQuotient (SubgroupFunctor.range d) q) :
    Smooth q.hom.hom.left := by
  let : IsAffineHom G.X.hom := hG.isAffineHom
  let : IsAffineHom Q.X.hom := hQ.isAffineHom
  let : IsClosedImmersion d.hom.hom.left := hd.1
  let : Mono d.hom.hom := Over.mono_of_mono_left _
  have hqc : QuasiCompact (q.hom.hom.left ≫ Q.X.hom) := by
    rw [Over.w q.hom.hom]
    infer_instance
  let : QuasiCompact (q.hom.hom.left ≫ Q.X.hom) := hqc
  let : QuasiCompact q.hom.hom.left := QuasiCompact.of_comp _ Q.X.hom
  exact hq.smooth_of_smooth_kernel ⟨inferInstance, rfl⟩ hd.2.2.1.smooth

/-- The full geometric kernels of an admissible quotient are semisimple. -/
theorem IsAdmissible.isSemisimple_geometricKernel {d : D ⟶ G}
    (hd : IsAdmissible d) {q : G ⟶ Q}
    (hq : RelativeRoot.IsFppfQuotient (SubgroupFunctor.range d) q) (s : S) :
    IsSemisimple (kernel ((baseChange (geometricPoint S s)).map q)) := by
  let : IsClosedImmersion d.hom.hom.left := hd.1
  let : Mono d.hom.hom := Over.mono_of_mono_left _
  let e : geometricFiber D s ≅ kernel ((baseChange (geometricPoint S s)).map q) :=
    (baseChange (geometricPoint S s)).mapIso
        (hq.kernelIso (show (SubgroupFunctor.range d).IsRepresentedBy d from
          ⟨inferInstance, rfl⟩)) ≪≫
      kernelBaseChangeIso (geometricPoint S s) q
  exact (hd.2.2.2.1 s).of_iso e.symm

/-- Every torus quotient supplied by admissibility is a smooth semisimple
torus quotient. -/
theorem IsAdmissible.isSemisimpleTorusQuotient (hG : IsReductive G)
    {d : D ⟶ G} (hd : IsAdmissible d) {q : G ⟶ Q}
    (hQ : RelativeTorus.IsTorus Q)
    (hq : RelativeRoot.IsFppfQuotient (SubgroupFunctor.range d) q) :
    IsSemisimpleTorusQuotient q :=
  ⟨hQ, hd.smooth_quotient hG hQ hq, hq.2.1,
    hd.isSemisimple_geometricKernel hq⟩

end RelativeDerived

/-- The geometric construction can equivalently produce a smooth surjective
torus quotient with semisimple full geometric kernels. -/
def RelativeDerivedTorusQuotientExistenceStatement : Prop :=
  ∀ (S : Scheme.{u}) (G : GroupScheme S), IsReductive G →
    ∃ (Q : GroupScheme S) (q : G ⟶ Q), RelativeDerived.IsSemisimpleTorusQuotient q

/-- The kernel construction and its converse identify the two existence
problems, without assuming either one. -/
theorem relativeDerivedGroupExistence_iff_torusQuotient :
    RelativeDerivedGroupExistenceStatement.{u} ↔
      RelativeDerivedTorusQuotientExistenceStatement.{u} := by
  constructor
  · intro hexists S G hG
    obtain ⟨D, d, hd⟩ := hexists S G hG
    obtain ⟨Q, q, hQ, hq⟩ := hd.2.2.2.2
    exact ⟨Q, q, hd.isSemisimpleTorusQuotient hG hQ hq⟩
  · intro hexists S G hG
    obtain ⟨Q, q, hq⟩ := hexists S G hG
    exact ⟨kernel q, kernelι q, RelativeDerived.isAdmissible_kernelι hG hq⟩

end Langlands.GroupScheme
