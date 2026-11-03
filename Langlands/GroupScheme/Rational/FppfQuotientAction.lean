import Langlands.GroupScheme.QuotientAction
import Langlands.GroupScheme.Reductive.UnipotentQuotient
import Langlands.GroupScheme.Rational.RootSubgroupStructureStatement
import Langlands.AlgebraicGeometry.SmoothEtaleSourceDescentProof
import Langlands.AlgebraicGeometry.SmoothConnectedRelativeDimensionProof
import Langlands.AlgebraicGeometry.FieldSmoothClosedPointStalkDimensionProof

/-! # Actions and dimension data on specified smooth fppf quotients -/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry
open scoped CategoryTheory.MonObj

namespace Langlands.GroupScheme

namespace AutomorphicAction

variable {B : Scheme.{u}} {H Z G : GroupScheme B}

/-- The range of an equivariant homomorphism is stable on every scheme test. -/
theorem IsEquivariant.isStable_range {aZ : AutomorphicAction H Z}
    {a : AutomorphicAction H G} {z : Z ⟶ G} (hz : aZ.IsEquivariant a z) :
    a.IsStable (SubgroupFunctor.range z) := by
  rintro T h g ⟨v, rfl⟩
  exact ⟨aZ.act h v, hz h v⟩

end AutomorphicAction

namespace RelativeRoot

section Action

variable {B : Scheme.{u}} {H G Q : GroupScheme B} {N : SubgroupFunctor G}
    {q : G ⟶ Q} (hq : IsFppfQuotient N q)
    (a : AutomorphicAction H G) (hN : a.IsStable N)

include hq in
/-- Every surjective fppf quotient of a connected group scheme is connected. -/
theorem IsFppfQuotient.connectedSpace [ConnectedSpace G.X.left] : ConnectedSpace Q.X.left :=
  hq.2.1.surj.connectedSpace q.hom.hom.left.continuous

variable [QuasiCompact q.hom.hom.left]

/-- The actual action on the specified quasi-compact fppf quotient by a stable
all-test subgroup functor. -/
def IsFppfQuotient.action : AutomorphicAction H Q :=
  letI : Flat q.hom.hom.left := hq.1
  letI : Surjective q.hom.hom.left := hq.2.1
  a.onQuotient q (by simpa only [hq.2.2.2] using hN)

/-- The given fppf quotient homomorphism intertwines the actions on every test. -/
theorem IsFppfQuotient.action_isEquivariant : a.IsEquivariant (hq.action a hN) q := by
  let : Flat q.hom.hom.left := hq.1
  let : Surjective q.hom.hom.left := hq.2.1
  intro T h g
  exact a.onQuotient_isEquivariant q (by simpa only [hq.2.2.2] using hN) h g

/-- Pointwise formula in the orientation used by the central quotient target. -/
theorem IsFppfQuotient.action_act {T : Over B} (h : T ⟶ H.X) (g : T ⟶ G.X) :
    (hq.action a hN).act h (g ≫ q.hom.hom) = a.act h g ≫ q.hom.hom :=
  (hq.action_isEquivariant a hN h g).symm

/-- Uniqueness of the action on the specified fppf quotient. -/
theorem IsFppfQuotient.action_unique (b : AutomorphicAction H Q)
    (hb : a.IsEquivariant b q) : b = hq.action a hN := by
  let : Flat q.hom.hom.left := hq.1
  let : Surjective q.hom.hom.left := hq.2.1
  exact a.onQuotient_unique q (by simpa only [hq.2.2.2] using hN) b hb

end Action

section Field

variable {k : Type u} [Field k]
    {H G Q : GroupScheme (Spec (CommRingCat.of k))} {N : SubgroupFunctor G}
    {q : G ⟶ Q} (hq : IsFppfQuotient N q)

include hq in
/-- Unipotence in the existing representation convention passes to every fppf
quotient. No quasi-compactness or smoothness assumption is needed. -/
theorem IsFppfQuotient.isUnipotent (hG : IsUnipotent G) : IsUnipotent Q := by
  let : Flat q.hom.hom.left := hq.1
  let : Surjective q.hom.hom.left := hq.2.1
  exact hG.of_flat_surjective q

theorem relativeDimension_eq {X : Scheme.{u}}
    (f : X ⟶ Spec (CommRingCat.of k)) [Nonempty X] {d e : ℕ}
    (hd : SmoothOfRelativeDimension d f) (he : SmoothOfRelativeDimension e f) : d = e := by
  let : SmoothOfRelativeDimension d f := hd
  let : Smooth f := SmoothOfRelativeDimension.smooth d f
  let : JacobsonSpace X := LocallyOfFiniteType.jacobsonSpace f
  obtain ⟨x, _, hx⟩ := nonempty_inter_closedPoints (Z := (Set.univ : Set X))
    Set.univ_nonempty isOpen_univ.isLocallyClosed
  have hxd := Langlands.AlgebraicGeometry.fieldSmoothClosedPointStalkDimension
    k X f d hd x hx
  have hxe := Langlands.AlgebraicGeometry.fieldSmoothClosedPointStalkDimension
    k X f e he x hx
  have hde := hxd.symm.trans hxe
  exact_mod_cast hde

include hq in
/-- Given an affine fppf quotient whose projection has positive prescribed
smooth dimension, the action and all other dimension-induction data follow.
The existence and affineness of the quotient, and the projection dimension,
are explicit inputs. -/
theorem IsFppfQuotient.exists_action_relativeDimension
    [IsAffineHom G.X.hom] [ConnectedSpace G.X.left] [IsAffineHom Q.X.hom]
    (hG : IsUnipotent G) (a : AutomorphicAction H G) (hN : a.IsStable N)
    {d n : ℕ} (hd : SmoothOfRelativeDimension d G.X.hom)
    (hn : SmoothOfRelativeDimension n q.hom.hom.left) (hpos : 0 < n) :
    ∃ (b : AutomorphicAction H Q) (m : ℕ),
      Smooth Q.X.hom ∧ ConnectedSpace Q.X.left ∧ IsUnipotent Q ∧
      SmoothOfRelativeDimension m Q.X.hom ∧ d = n + m ∧ m < d ∧
      ∀ (T : Over (Spec (CommRingCat.of k))) (h : T ⟶ H.X) (g : T ⟶ G.X),
        b.act h (g ≫ q.hom.hom) = a.act h g ≫ q.hom.hom := by
  let : SmoothOfRelativeDimension d G.X.hom := hd
  let : SmoothOfRelativeDimension n q.hom.hom.left := hn
  let : Smooth G.X.hom := SmoothOfRelativeDimension.smooth d G.X.hom
  let : Smooth q.hom.hom.left := SmoothOfRelativeDimension.smooth n q.hom.hom.left
  let : Surjective q.hom.hom.left := hq.2.1
  have hcomp : Smooth (q.hom.hom.left ≫ Q.X.hom) := by
    rw [Over.w q.hom.hom]
    infer_instance
  let : Smooth (q.hom.hom.left ≫ Q.X.hom) := hcomp
  let : Smooth Q.X.hom :=
    Langlands.AlgebraicGeometry.smooth_of_smooth_of_surjective_of_smooth_comp
      q.hom.hom.left Q.X.hom
  let : ConnectedSpace Q.X.left := hq.connectedSpace
  obtain ⟨m, hm⟩ := Langlands.AlgebraicGeometry.smoothConnectedRelativeDimension
    Q.X.left _ Q.X.hom inferInstance inferInstance
  let : SmoothOfRelativeDimension m Q.X.hom := hm
  have hsum : SmoothOfRelativeDimension (n + m) G.X.hom := by
    rw [← Over.w q.hom.hom]
    infer_instance
  have heq : d = n + m := relativeDimension_eq G.X.hom hd hsum
  have hqc : QuasiCompact (q.hom.hom.left ≫ Q.X.hom) := by
    rw [Over.w q.hom.hom]
    infer_instance
  let : QuasiCompact (q.hom.hom.left ≫ Q.X.hom) := hqc
  let : QuasiCompact q.hom.hom.left := QuasiCompact.of_comp q.hom.hom.left Q.X.hom
  refine ⟨hq.action a hN, m, inferInstance, inferInstance, hq.isUnipotent hG,
    hm, heq, ?_, ?_⟩
  · omega
  · intro T h g
    exact hq.action_act a hN h g

end Field

end RelativeRoot
end Langlands.GroupScheme
