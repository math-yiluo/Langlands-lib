import Langlands.GroupScheme.Torus.MultiplicativeTypeExtensionActionStatement
import Langlands.GroupScheme.Torus.MultiplicativeTypeHomFamily
import Langlands.GroupScheme.Torus.MultiplicativeTypeGeometry
import Langlands.GroupScheme.RepresentedAction
import Langlands.GroupScheme.Rational.FppfQuotientAction

/-! # Central extensions of multiplicative type: rigidity inputs and the closing step

Assuming `DiagonalizableRigidityStatement`, a natural family of homomorphisms between two groups
of multiplicative type, parametrized by a connected algebraic group, does not depend on the
parameter (`homFamily_eq`). Hence a connected algebraic group acts trivially on a group of
multiplicative type (`act_eq_self`). Under the hypotheses of
`MultiplicativeTypeExtensionActionStatement`, the given action therefore fixes every point of
the central subgroup `N` (`act_comp_eq`) and induces the trivial action on the quotient `Q`
(`act_comp_quotient`). Conversely, once `g · x = x · j (ψ (g, p x))` for a family `ψ` that does
not depend on `g`, the action is trivial (`act_eq_of_difference`). -/

noncomputable section

universe u

open CategoryTheory CategoryTheory.MonoidalCategory
open CategoryTheory.CartesianMonoidalCategory AlgebraicGeometry
open scoped CategoryTheory.MonObj

namespace Langlands.GroupScheme.MultiplicativeTypeExtensionAction

variable {k : Type u} [Field k] {G H N Q : GroupScheme (Spec (CommRingCat.of k))}
  {j : N ⟶ H} {p : H ⟶ Q}

/-- **Rigidity of homomorphism families between groups of multiplicative type.** A natural
family of homomorphisms `Q → N` parametrized by a connected algebraic group `G` takes the same
value at every parameter as at the identity. This restates the published
`HomFamily.eq_one_of_multiplicativeType` with the hypotheses on `G` as explicit arguments. -/
theorem homFamily_eq (hRig : DiagonalizableRigidityStatement.{u})
    (hGft : LocallyOfFiniteType G.X.hom) (hGqc : QuasiCompact G.X.hom)
    (hGc : ConnectedSpace G.X.left) (hQ : IsMultiplicativeType Q) (hN : IsMultiplicativeType N)
    {F : ∀ T : Over (Spec (CommRingCat.of k)), (T ⟶ G.X) → (T ⟶ Q.X) → (T ⟶ N.X)}
    (hF : HomFamily.IsHomFamily F) {T : Over (Spec (CommRingCat.of k))}
    (g : T ⟶ G.X) (q : T ⟶ Q.X) : F T g q = F T 1 q := by
  have : LocallyOfFiniteType G.X.hom := hGft
  have : QuasiCompact G.X.hom := hGqc
  have : ConnectedSpace G.X.left := hGc
  exact HomFamily.eq_one_of_multiplicativeType hRig hQ hN hF g q

/-- **A connected algebraic group acts trivially on a group of multiplicative type.** The
action points form a homomorphism family parametrized by the acting group. -/
theorem act_eq_self (hRig : DiagonalizableRigidityStatement.{u})
    (hGft : LocallyOfFiniteType G.X.hom) (hGqc : QuasiCompact G.X.hom)
    (hGc : ConnectedSpace G.X.left) (hN : IsMultiplicativeType N)
    (a : AutomorphicAction G N) {T : Over (Spec (CommRingCat.of k))}
    (g : T ⟶ G.X) (x : T ⟶ N.X) : a.act g x = x := by
  have hF : HomFamily.IsHomFamily (U := G.X) (fun _ g x => a.act g x) :=
    ⟨fun _ g x y => a.act_mul_right g x y, fun f g x => (a.naturality f g x).symm⟩
  simpa only [a.act_one_left] using homFamily_eq hRig hGft hGqc hGc hN hN hF g x

/-- A closed subgroup represents its range. -/
theorem isRepresentedBy_range (hj : IsClosedSubgroup j) :
    (SubgroupFunctor.range j).IsRepresentedBy j := by
  have : IsClosedImmersion j.hom.hom.left := hj
  exact ⟨Over.mono_of_mono_left _, rfl⟩

/-- An fppf quotient map from a quasi-compact group onto an affine group is quasi-compact. -/
theorem quasiCompact_quotient [QuasiCompact H.X.hom] [IsAffine Q.X.left] :
    QuasiCompact p.hom.hom.left := by
  have hqc : QuasiCompact (p.hom.hom.left ≫ Q.X.hom) := by
    rw [Over.w p.hom.hom]
    infer_instance
  exact QuasiCompact.of_comp p.hom.hom.left Q.X.hom

/-- **The action fixes the central subgroup.** If a connected algebraic group `G` acts on `H`
by group automorphisms preserving the closed subgroup `N` of multiplicative type, then every
point of `N` is fixed. The proof restricts the action to `N` and applies `act_eq_self`. -/
theorem act_comp_eq (hRig : DiagonalizableRigidityStatement.{u})
    (hGft : LocallyOfFiniteType G.X.hom) (hGqc : QuasiCompact G.X.hom)
    (hGc : ConnectedSpace G.X.left) (hj : IsClosedSubgroup j) (hN : IsMultiplicativeType N)
    (a : AutomorphicAction G H)
    (ha : ∀ (T : Over (Spec (CommRingCat.of k))) (g : T ⟶ G.X) (x : T ⟶ H.X),
      x ∈ (SubgroupFunctor.range j).carrier T →
        a.act g x ∈ (SubgroupFunctor.range j).carrier T)
    {T : Over (Spec (CommRingCat.of k))} (g : T ⟶ G.X) (n : T ⟶ N.X) :
    a.act g (n ≫ j.hom.hom) = n ≫ j.hom.hom := by
  have hi := isRepresentedBy_range hj
  rw [← AutomorphicAction.onRepresentedSubgroup_act_comp a j hi ha g n,
    act_eq_self hRig hGft hGqc hGc hN (a.onRepresentedSubgroup j hi ha) g n]

/-- **The induced action on the quotient is trivial.** Under the same hypotheses, with `p` an
fppf quotient of `H` by `N` and `Q` of multiplicative type, `p (g · x) = p x` for all points.
The proof passes the action to `Q` (`RelativeRoot.IsFppfQuotient.action`; `Q` is affine, so `p`
is quasi-compact) and applies `act_eq_self`. -/
theorem act_comp_quotient (hRig : DiagonalizableRigidityStatement.{u})
    (hGft : LocallyOfFiniteType G.X.hom) (hGqc : QuasiCompact G.X.hom)
    (hGc : ConnectedSpace G.X.left) (hHqc : QuasiCompact H.X.hom)
    (hp : RelativeRoot.IsFppfQuotient (SubgroupFunctor.range j) p)
    (hQ : IsMultiplicativeType Q) (a : AutomorphicAction G H)
    (ha : ∀ (T : Over (Spec (CommRingCat.of k))) (g : T ⟶ G.X) (x : T ⟶ H.X),
      x ∈ (SubgroupFunctor.range j).carrier T →
        a.act g x ∈ (SubgroupFunctor.range j).carrier T)
    {T : Over (Spec (CommRingCat.of k))} (g : T ⟶ G.X) (x : T ⟶ H.X) :
    a.act g x ≫ p.hom.hom = x ≫ p.hom.hom := by
  have : IsAffine Q.X.left := hQ.isAffine
  have : QuasiCompact p.hom.hom.left := quasiCompact_quotient
  rw [← hp.action_act a ha g x,
    act_eq_self hRig hGft hGqc hGc hQ (hp.action a ha) g (x ≫ p.hom.hom)]

/-- **Closing step.** If `g · x = x · j(ψ(g, p x))` for a morphism `ψ : G × Q → N` that does
not depend on its first argument, then the action is trivial: the value at `g` equals the
value at the identity, where the action is trivial. -/
theorem act_eq_of_difference (a : AutomorphicAction G H) (ψ : G.X ⊗ Q.X ⟶ N.X)
    (hψ : ∀ (T : Over (Spec (CommRingCat.of k))) (g : T ⟶ G.X) (x : T ⟶ H.X),
      a.act g x = x * (lift g (x ≫ p.hom.hom) ≫ ψ ≫ j.hom.hom))
    (hrig : ∀ (T : Over (Spec (CommRingCat.of k))) (g : T ⟶ G.X) (q : T ⟶ Q.X),
      lift g q ≫ ψ = lift 1 q ≫ ψ)
    {T : Over (Spec (CommRingCat.of k))} (g : T ⟶ G.X) (x : T ⟶ H.X) :
    a.act g x = x := by
  rw [hψ, ← Category.assoc, hrig, Category.assoc, ← hψ, a.act_one_left]

end Langlands.GroupScheme.MultiplicativeTypeExtensionAction
