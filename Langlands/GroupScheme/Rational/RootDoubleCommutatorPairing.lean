import Langlands.GroupScheme.CentralIsogeny.CommutatorPairing
import Langlands.GroupScheme.Rational.RootSubgroupCentrality
import Langlands.GroupScheme.Rational.RootSubgroupWeightCoordinates
import Langlands.GroupScheme.Rational.SemigroupTransport
import Langlands.GroupScheme.Rational.SemigroupRealizationProof
import Langlands.GroupScheme.Rational.SemigroupCommutatorProof
import Langlands.GroupScheme.Rational.CyclicWeightFiltrationProof
import Langlands.GroupScheme.FieldSeparatedProof

/-! # The commutator pairing of a multipliable relative-root subgroup -/

noncomputable section

universe u

open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory
open CategoryTheory.CartesianMonoidalCategory AlgebraicGeometry
open scoped CategoryTheory.MonObj

namespace Langlands.GroupScheme.RelativeRoot

variable {k : Type u} [Field k]
    {S : CommGroupScheme (Spec (CommRingCat.of k))}
    {G : GroupScheme (Spec (CommRingCat.of k))}
    {U U₂ : GroupScheme (Spec (CommRingCat.of k))}

/-- A represented fppf quotient `q : U_a → V` by the doubled root subgroup, with the
equivariant vector structure of weight `a` on `V`, together with the commutator pairing
`V × V → U_{2a}`: on lifted points it is the commutator of the lifts in `G`. -/
structure DoubleRootCommutatorPairing (i : S.toGrp ⟶ G) (a : characterLattice S)
    {j : U ⟶ G} (hj : (subgroup i a).IsRepresentedBy j)
    {j₂ : U₂ ⟶ G} (hj₂ : (subgroup i (2 • a)).IsRepresentedBy j₂) where
  /-- The quotient of the root group by the doubled root group. -/
  V : GroupScheme (Spec (CommRingCat.of k))
  /-- The quotient homomorphism. -/
  q : U ⟶ V
  /-- The torus action on the quotient. -/
  action : AutomorphicAction S.toGrp V
  isFppfQuotient : IsFppfQuotient ((subgroup i (2 • a)).comap j) q
  quasiCompact : QuasiCompact q.hom.hom.left
  weightVectorStructure : HasUniqueWeightVectorStructure action a
  act_comp : ∀ (T : Over (Spec (CommRingCat.of k))) (s : T ⟶ S.X) (h : T ⟶ U.X),
    action.act s (h ≫ q.hom.hom) = (subgroupAction i a j hj).act s h ≫ q.hom.hom
  /-- The commutator pairing, with values in the doubled root group. -/
  pairing : V.X ⊗ V.X ⟶ U₂.X
  lift_pairing : ∀ (T : Over (Spec (CommRingCat.of k))) (g h : T ⟶ U.X),
    (lift (g ≫ q.hom.hom) (h ≫ q.hom.hom) ≫ pairing) ≫ j₂.hom.hom =
      (g ≫ j.hom.hom) * (h ≫ j.hom.hom) * (g ≫ j.hom.hom)⁻¹ * (h ≫ j.hom.hom)⁻¹
  lift_mul_pairing : ∀ (T : Over (Spec (CommRingCat.of k))) (x x' y : T ⟶ V.X),
    lift (x * x') y ≫ pairing = (lift x y ≫ pairing) * (lift x' y ≫ pairing)
  lift_pairing_mul : ∀ (T : Over (Spec (CommRingCat.of k))) (x y y' : T ⟶ V.X),
    lift x (y * y') ≫ pairing = (lift x y ≫ pairing) * (lift x y' ≫ pairing)
  lift_self_pairing : ∀ (T : Over (Spec (CommRingCat.of k))) (x : T ⟶ V.X),
    lift x x ≫ pairing = 1
  lift_pairing_act : ∀ (T : Over (Spec (CommRingCat.of k))) (s : T ⟶ S.X) (x y : T ⟶ V.X),
    lift (action.act s x) (action.act s y) ≫ pairing =
      (subgroupAction i (2 • a) j₂ hj₂).act s (lift x y ≫ pairing)

section Construction

variable [IsAffineHom G.X.hom] [Smooth G.X.hom]

/-- Points of a group scheme with vector coordinates commute. -/
theorem commute_of_hasUniqueWeightVectorStructure {V : GroupScheme (Spec (CommRingCat.of k))}
    {c : AutomorphicAction S.toGrp V} {χ : characterLattice S}
    (hc : HasUniqueWeightVectorStructure c χ) (T : Over (Spec (CommRingCat.of k)))
    (x y : T ⟶ V.X) : Commute x y := by
  obtain ⟨n, e, -⟩ := hc.1
  apply (e T).injective
  rw [map_mul, map_mul, mul_comm]

/-- With no positive multiple beyond the double a root, every point of the doubled root
subgroup commutes with every point of the root subgroup, read in a representative. -/
theorem commute_comap_double_of_noHigherRoots (hS : IsSplitTorus S.toGrp)
    (i : S.toGrp ⟶ G) {a : characterLattice S} (ha : a ≠ 0)
    (hhigh : ∀ n : ℕ, 3 ≤ n → n • a ∉ relativeRoots i)
    {j : U ⟶ G} (hj : (subgroup i a).IsRepresentedBy j)
    (T : Over (Spec (CommRingCat.of k))) (x y : T ⟶ U.X)
    (hx : x ∈ ((subgroup i (2 • a)).comap j).carrier T) : Commute x y := by
  let : Mono j.hom.hom := hj.1
  have hy : y ≫ j.hom.hom ∈ (subgroup i a).carrier T := by
    rw [← hj.2]
    exact ⟨y, rfl⟩
  have hc := double_subgroup_commute_of_noHigherRoots semigroupRealization
    semigroupCommutator cyclicRootFunctorComparison inferInstance hS i ha hhigh T
    (x ≫ j.hom.hom) (y ≫ j.hom.hom) hx hy
  apply (cancel_mono j.hom.hom).mp
  rw [MonObj.mul_comp, MonObj.mul_comp]
  exact hc.eq

variable [QuasiCompact U.X.hom]

/-- Existence of the commutator pairing of a multipliable root whose higher multiples are
not roots, for every representative of the root group and of the doubled root group. -/
theorem nonempty_doubleRootCommutatorPairing (hS : IsSplitTorus S.toGrp)
    (i : S.toGrp ⟶ G) {a : characterLattice S} (ha : a ≠ 0)
    (hhigh : ∀ n : ℕ, 3 ≤ n → n • a ∉ relativeRoots i)
    {j : U ⟶ G} (hj : (subgroup i a).IsRepresentedBy j)
    {j₂ : U₂ ⟶ G} (hj₂ : (subgroup i (2 • a)).IsRepresentedBy j₂) :
    Nonempty (DoubleRootCommutatorPairing i a hj hj₂) := by
  let b := AutomorphicAction.conjugation i
  let : Mono j.hom.hom := hj.1
  have h2a : 2 • a ≠ 0 := hS.nsmul_ne_zero ha (by omega)
  have hfirst : weightFiltration b a 1 = subgroup i a :=
    cyclicRootFunctorComparison k G inferInstance inferInstance S hS i a ha
  have hrep : (weightFiltration b a 1).IsRepresentedBy j := hfirst.symm ▸ hj
  obtain ⟨V, q, c, d, hq, hc, hjd, hqd⟩ :=
    (cyclicWeightFiltration k G inferInstance inferInstance S hS b a ha 1
      (by decide)).2 U j hrep
  have hweights : ∀ n : ℕ, 3 ≤ n → n • a ∉ actionWeightSupport b ⊤ := by
    intro n hn hsupp
    exact hhigh n hn ((mem_actionWeightSupport_conjugation_iff i
      (hS.nsmul_ne_zero ha (by omega))).mp hsupp)
  have htwo : weightFiltration b a 2 = subgroup i (2 • a) := by
    rw [weightFiltration_two_eq_double b a hweights]
    exact cyclicRootFunctorComparison k G inferInstance inferInstance S hS i (2 • a) h2a
  have hq' : IsFppfQuotient ((subgroup i (2 • a)).comap j) q := by
    simpa only [show 1 + 1 = (2 : ℕ) from rfl, htwo] using hq
  have hc' : HasUniqueWeightVectorStructure c a := by simpa only [one_nsmul] using hc
  have hdc : ∀ (T : Over (Spec (CommRingCat.of k))) (s : T ⟶ S.X) (h : T ⟶ U.X),
      c.act s (h ≫ q.hom.hom) = (subgroupAction i a j hj).act s h ≫ q.hom.hom := by
    intro T s h
    rw [hqd]
    congr 1
    apply (cancel_mono j.hom.hom).mp
    rw [subgroupAction_act_comp, hjd, AutomorphicAction.conjugation_act]
  let : Flat q.hom.hom.left := hq'.1
  let : Surjective q.hom.hom.left := hq'.2.1
  let : IsSeparated V.X.hom := fieldSeparated k V
  have hqc : QuasiCompact (q.hom.hom.left ≫ V.X.hom) := by
    rw [Over.w q.hom.hom]
    infer_instance
  let : QuasiCompact q.hom.hom.left := QuasiCompact.of_comp _ V.X.hom
  have hπ : IsCentral (kernelι q) :=
    isCentral_kernelι_of_commute q hq'.2.2.2
      (commute_comap_double_of_noHigherRoots hS i ha hhigh hj)
  have hV := commute_of_hasUniqueWeightVectorStructure hc'
  have hle : subgroup i (2 • a) ≤ subgroup i a :=
    double_subgroup_le_of_cyclicComparison cyclicRootFunctorComparison inferInstance hS i ha
  have hκ' := SubgroupFunctor.IsRepresentedBy.factor hj hj₂ hle
  have hκ : (SubgroupFunctor.range (kernelι q)).IsRepresentedBy
      (hj.factorHom j₂ (by rw [hj₂.2]; exact hle)) := by
    rw [hq'.2.2.2]
    exact hκ'
  have hκj : (hj.factorHom j₂ (by rw [hj₂.2]; exact hle)).hom.hom ≫ j.hom.hom =
      j₂.hom.hom :=
    congrArg (fun f => f.hom.hom) (hj.factorHom_comp j₂ _)
  have hac : ∀ (T : Over (Spec (CommRingCat.of k))) (s : T ⟶ S.X) (l : T ⟶ U₂.X),
      (subgroupAction i a j hj).act s
          (l ≫ (hj.factorHom j₂ (by rw [hj₂.2]; exact hle)).hom.hom) =
        (subgroupAction i (2 • a) j₂ hj₂).act s l ≫
          (hj.factorHom j₂ (by rw [hj₂.2]; exact hle)).hom.hom := by
    intro T s l
    apply (cancel_mono j.hom.hom).mp
    rw [subgroupAction_act_comp, Category.assoc, Category.assoc, hκj,
      subgroupAction_act_comp]
  refine ⟨{
    V := V
    q := q
    action := c
    isFppfQuotient := hq'
    quasiCompact := inferInstance
    weightVectorStructure := hc'
    act_comp := hdc
    pairing := CommutatorDescent.pairing q hπ hV hκ
    lift_pairing := ?_
    lift_mul_pairing := fun T x x' y => CommutatorDescent.lift_mul_pairing q hπ hV hκ x x' y
    lift_pairing_mul := fun T x y y' => CommutatorDescent.lift_pairing_mul q hπ hV hκ x y y'
    lift_self_pairing := fun T x => CommutatorDescent.lift_self_pairing q hπ hV hκ x
    lift_pairing_act := fun T s x y => CommutatorDescent.lift_pairing_act q hπ hV hκ
      (subgroupAction i a j hj) c (subgroupAction i (2 • a) j₂ hj₂)
      (fun T s g => hdc T s g) hac s x y }⟩
  intro T g h
  calc (lift (g ≫ q.hom.hom) (h ≫ q.hom.hom) ≫ CommutatorDescent.pairing q hπ hV hκ) ≫
        j₂.hom.hom
      = ((lift (g ≫ q.hom.hom) (h ≫ q.hom.hom) ≫ CommutatorDescent.pairing q hπ hV hκ) ≫
          (hj.factorHom j₂ (by rw [hj₂.2]; exact hle)).hom.hom) ≫ j.hom.hom := by
        rw [Category.assoc _ _ j.hom.hom, hκj]
    _ = (g * h * g⁻¹ * h⁻¹) ≫ j.hom.hom := by rw [CommutatorDescent.lift_pairing]
    _ = _ := by
        rw [MonObj.mul_comp, MonObj.mul_comp, MonObj.mul_comp, GrpObj.inv_comp,
          GrpObj.inv_comp]

/-- A chosen commutator pairing of a multipliable root whose higher multiples are not
roots. -/
def doubleRootCommutatorPairing (hS : IsSplitTorus S.toGrp)
    (i : S.toGrp ⟶ G) {a : characterLattice S} (ha : a ≠ 0)
    (hhigh : ∀ n : ℕ, 3 ≤ n → n • a ∉ relativeRoots i)
    {j : U ⟶ G} (hj : (subgroup i a).IsRepresentedBy j)
    {j₂ : U₂ ⟶ G} (hj₂ : (subgroup i (2 • a)).IsRepresentedBy j₂) :
    DoubleRootCommutatorPairing i a hj hj₂ :=
  Classical.choice (nonempty_doubleRootCommutatorPairing hS i ha hhigh hj hj₂)

end Construction

end Langlands.GroupScheme.RelativeRoot
