import Langlands.GroupScheme.Reductive.NormalUnipotentRadicalIntersectionStatement
import Langlands.GroupScheme.Reductive.UnipotentRadicalQuotientProof
import Langlands.GroupScheme.Reductive.PerfectFieldStatement
import Langlands.GroupScheme.Rational.SemigroupNormalReductiveReduction
import Langlands.GroupScheme.Rational.SemigroupQuotientTransport
import Langlands.GroupScheme.Rational.SemigroupRealizationProof
import Langlands.GroupScheme.Rational.SemigroupSmoothQuotientProof
import Langlands.GroupScheme.Rational.FppfQuotientSmooth
import Langlands.GroupScheme.Rational.SolvableSchemeComparison
import Langlands.GroupScheme.SchemeActionProperFixedFromAffine

/-! # Normal semigroup comparison through unipotent radical quotients -/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry
open scoped CategoryTheory.MonObj

namespace Langlands.GroupScheme.RelativeRoot

/-- The independent structural propositions used in the normal radical
reduction. Radical stability and quotient reductivity remain separate inputs. -/
def NormalSemigroupRadicalPrerequisites : Prop :=
  NormalUnipotentRadicalIntersectionStatement.{u} ∧
    NormalReductiveSemigroupPrerequisites.{u} ∧
    Torus.SolvableFixedContainmentConnectedStatement.{u}

section SuppliedQuotients

variable {k : Type u} [Field k] [IsAlgClosed k]
    {G H U V Q R : GroupScheme (Spec (CommRingCat.of k))}
    [Smooth G.X.hom] [Smooth H.X.hom]
    [IsAffineHom G.X.hom] [IsAffineHom H.X.hom]
    [ConnectedSpace G.X.left] [ConnectedSpace H.X.left]
    {S : CommGroupScheme (Spec (CommRingCat.of k))}

/-- Supplied stable radicals and reductive fppf radical quotients reduce normal
semigroup intersection comparison to the displayed structural propositions. -/
theorem semigroup_comap_eq_of_normal_radical_quotients
    (hPrerequisites : NormalSemigroupRadicalPrerequisites.{u})
    (hS : IsSplitTorus S.toGrp)
    (b : AutomorphicAction S.toGrp G) (c : AutomorphicAction S.toGrp H)
    (i : H ⟶ G) (hi : IsClosedSubgroup i)
    (hn : (SubgroupFunctor.range i).IsNormal)
    (heq : ∀ (T : Over (Spec (CommRingCat.of k))) (t : T ⟶ S.X) (h : T ⟶ H.X),
      c.act t h ≫ i.hom.hom = b.act t (h ≫ i.hom.hom))
    (r : U ⟶ G) (s : V ⟶ H)
    (hr : IsUnipotentRadical r) (hs : IsUnipotentRadical s)
    (hstableU : b.IsStable (SubgroupFunctor.range r))
    (hstableV : c.IsStable (SubgroupFunctor.range s))
    (q : G ⟶ Q) (p : H ⟶ R)
    (hq : IsFppfQuotient (SubgroupFunctor.range r) q)
    (hp : IsFppfQuotient (SubgroupFunctor.range s) p)
    (hQ : IsConnectedReductive Q) (hR : IsConnectedReductive R)
    (A : AddSubsemigroup (characterLattice S)) (hzero : 0 ∈ A) :
    (semigroupSubgroup b A).comap i = semigroupSubgroup c A := by
  let : Smooth Q.X.hom := hQ.smooth
  let : Smooth R.X.hom := hR.smooth
  let : IsAffineHom Q.X.hom := hQ.isAffineHom
  let : IsAffineHom R.X.hom := hR.isAffineHom
  let : ConnectedSpace R.X.left := hR.connectedSpace
  let : Flat q.hom.hom.left := hq.1
  let : Surjective q.hom.hom.left := hq.2.1
  let : Flat p.hom.hom.left := hp.1
  let : Surjective p.hom.hom.left := hp.2.1
  have hqc : QuasiCompact (q.hom.hom.left ≫ Q.X.hom) := by
    rw [Over.w q.hom.hom]
    infer_instance
  let : QuasiCompact (q.hom.hom.left ≫ Q.X.hom) := hqc
  let : QuasiCompact q.hom.hom.left := QuasiCompact.of_comp q.hom.hom.left Q.X.hom
  have hpc : QuasiCompact (p.hom.hom.left ≫ R.X.hom) := by
    rw [Over.w p.hom.hom]
    infer_instance
  let : QuasiCompact (p.hom.hom.left ≫ R.X.hom) := hpc
  let : QuasiCompact p.hom.hom.left := QuasiCompact.of_comp p.hom.hom.left R.X.hom
  let : IsClosedImmersion s.hom.hom.left := hs.isClosedSubgroup
  let : Mono s.hom.hom := Over.mono_of_mono_left _
  let : Smooth V.X.hom := hs.smooth
  let : ConnectedSpace V.X.left := hs.connectedSpace
  let : IsAffineHom V.X.hom := by
    rw [← Over.w s.hom.hom]
    infer_instance
  have hsrep : (SubgroupFunctor.range s).IsRepresentedBy s := ⟨inferInstance, rfl⟩
  let b' := hq.action b hstableU
  let c' := hp.action c hstableV
  let d := c.onRepresentedSubgroup s hsrep hstableV
  obtain ⟨j, hsq, hj, hjn⟩ :=
    exists_normal_quotientSubgroupHom_of_normalUnipotentRadicalIntersectionStatement
      hPrerequisites.1 i hi hn r s hr hs q p hq.2.2.2 hp.2.2.2
  have heqj : ∀ (T : Over (Spec (CommRingCat.of k))) (t : T ⟶ S.X) (x : T ⟶ R.X),
      c'.act t x ≫ j.hom.hom = b'.act t (x ≫ j.hom.hom) := by
    have hsq' : i.hom.hom ≫ q.hom.hom = p.hom.hom ≫ j.hom.hom :=
      congrArg (fun f => f.hom.hom) hsq
    intro T t x
    apply AutomorphicAction.hom_ext_of_local_quotient_lift p x
    intro W a y hy
    simp only [← Category.assoc, c'.naturality, b'.naturality]
    rw [hy, ← hp.action_isEquivariant c hstableV, Category.assoc, ← hsq',
      ← Category.assoc, heq, Category.assoc, hq.action_isEquivariant b hstableU]
    simp only [Category.assoc, hsq']
    rfl
  have hquot := semigroup_comap_eq_of_normalReductive hPrerequisites.2.1 hQ hR
    hS b' c' j hj hjn heqj A hzero
  have hsolv : IsSolvableScheme V :=
    isSolvableScheme_of_isSolvableGroupScheme hs.smooth
      (isSolvableGroupScheme_of_isUnipotent hs.isUnipotent)
  exact semigroup_comap_eq_of_smooth_quotient_of_solvable_kernel
    hS b c b' c' d i q p j s heq
    (fun _ t g => hq.action_isEquivariant b hstableU t g)
    (fun _ t x => c.onRepresentedSubgroup_act_comp s hsrep hstableV t x)
    hPrerequisites.2.2 hsolv semigroupRealization semigroupSmoothQuotient
    hi hs.isClosedSubgroup hsq
    (fun _ t h => hp.action_isEquivariant c hstableV t h)
    (hp.smooth_of_smooth_kernel hsrep hs.smooth) hp.2.1 hp.2.2.2 A hzero hquot

end SuppliedQuotients

section Existence

variable {k : Type u} [Field k] [IsAlgClosed k]
    {G H U V : GroupScheme (Spec (CommRingCat.of k))}
    [Smooth G.X.hom] [Smooth H.X.hom]
    [IsAffineHom G.X.hom] [IsAffineHom H.X.hom]
    [ConnectedSpace G.X.left] [ConnectedSpace H.X.left]
    {S : CommGroupScheme (Spec (CommRingCat.of k))}

/-- Actual radical quotient existence supplies the quotient data. The
perfect-field comparison and both radical stability premises remain explicit. -/
theorem semigroup_comap_eq_of_normal_stable_radicals
    (hPrerequisites : NormalSemigroupRadicalPrerequisites.{u})
    (hPerfect : PerfectFieldPseudoReductiveStatement.{u})
    (hS : IsSplitTorus S.toGrp)
    (b : AutomorphicAction S.toGrp G) (c : AutomorphicAction S.toGrp H)
    (i : H ⟶ G) (hi : IsClosedSubgroup i)
    (hn : (SubgroupFunctor.range i).IsNormal)
    (heq : ∀ (T : Over (Spec (CommRingCat.of k))) (t : T ⟶ S.X) (h : T ⟶ H.X),
      c.act t h ≫ i.hom.hom = b.act t (h ≫ i.hom.hom))
    (r : U ⟶ G) (s : V ⟶ H)
    (hr : IsUnipotentRadical r) (hs : IsUnipotentRadical s)
    (hstableU : b.IsStable (SubgroupFunctor.range r))
    (hstableV : c.IsStable (SubgroupFunctor.range s))
    (A : AddSubsemigroup (characterLattice S)) (hzero : 0 ∈ A) :
    (semigroupSubgroup b A).comap i = semigroupSubgroup c A := by
  obtain ⟨Q, q, hq, hQ⟩ := unipotentRadicalQuotient k G U r hr
  obtain ⟨R, p, hp, hR⟩ := unipotentRadicalQuotient k H V s hs
  exact semigroup_comap_eq_of_normal_radical_quotients hPrerequisites hS b c i hi hn
    heq r s hr hs hstableU hstableV q p hq hp
    ((hPerfect k Q).1 hQ) ((hPerfect k R).1 hR) A hzero

end Existence

end Langlands.GroupScheme.RelativeRoot
