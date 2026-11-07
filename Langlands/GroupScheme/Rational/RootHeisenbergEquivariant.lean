import Langlands.GroupScheme.Rational.RootHeisenbergNormalForm
import Langlands.GroupScheme.Rational.TorusEquivariantSection
import Langlands.GroupScheme.Rational.RootSubgroupCentralizerAction
import Langlands.GroupScheme.Rational.FppfQuotientAction

/-! # Heisenberg normal forms equivariant for a torus fixing the split torus

Let a group scheme `D` act on `G` fixing the split torus `S`. Then `D` acts on the root group
`U_a`, on the doubled root group `U_{2a}` and on the quotient `U_a / U_{2a}`. If `D` is a torus
through which the action of `S` factors, the Heisenberg normal form can be chosen with a section
that is equivariant for `D`. Its cocycle and the commutator pairing are then `D`-equivariant.
-/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry
open CategoryTheory.Limits CategoryTheory.MonoidalCategory CategoryTheory.CartesianMonoidalCategory
open scoped CategoryTheory.MonObj

namespace Langlands.GroupScheme.RelativeRoot

section Actions

variable {k : Type u} [Field k] {S : CommGroupScheme (Spec (CommRingCat.of k))}
    {G U D : GroupScheme (Spec (CommRingCat.of k))}
    {i : S.toGrp ⟶ G} (b : AutomorphicAction D G)
    (hfix : ∀ (T : Over (Spec (CommRingCat.of k))) (z : T ⟶ D.X) (t : T ⟶ S.X),
      b.act z (t ≫ i.hom.hom) = t ≫ i.hom.hom)
    {a : characterLattice S} {j : U ⟶ G} (hj : (subgroup i a).IsRepresentedBy j)

/-- The action of a group fixing the torus commutes with the torus action on a root group. -/
theorem rootActionOfFixesTorus_commute {T : Over (Spec (CommRingCat.of k))} (z : T ⟶ D.X)
    (t : T ⟶ S.X) (g : T ⟶ U.X) :
    (rootActionOfFixesTorus b i hfix a j hj).act z ((subgroupAction i a j hj).act t g) =
      (subgroupAction i a j hj).act t ((rootActionOfFixesTorus b i hfix a j hj).act z g) := by
  let : Mono j.hom.hom := hj.1
  apply (cancel_mono j.hom.hom).1
  rw [rootActionOfFixesTorus_act_comp, subgroupAction_act_comp, subgroupAction_act_comp,
    rootActionOfFixesTorus_act_comp, b.act_mul_right, b.act_mul_right, b.act_inv, hfix]

/-- If the torus action factors through `D`, the two actions on a root group agree. -/
theorem subgroupAction_eq_rootActionOfFixesTorus (s : S.toGrp ⟶ D)
    (hs : ∀ (T : Over (Spec (CommRingCat.of k))) (t : T ⟶ S.X) (g : T ⟶ G.X),
      b.act (t ≫ s.hom.hom) g = (t ≫ i.hom.hom) * g * (t ≫ i.hom.hom)⁻¹)
    {T : Over (Spec (CommRingCat.of k))} (t : T ⟶ S.X) (g : T ⟶ U.X) :
    (subgroupAction i a j hj).act t g =
      (rootActionOfFixesTorus b i hfix a j hj).act (t ≫ s.hom.hom) g := by
  let : Mono j.hom.hom := hj.1
  apply (cancel_mono j.hom.hom).1
  rw [subgroupAction_act_comp, rootActionOfFixesTorus_act_comp, hs]

/-- **Linearity.** For a nonzero root and weight vector coordinates on its root group, an
affine group fixing the torus acts linearly. -/
theorem isLinearVectorCoordinates_rootActionOfFixesTorus [IsAffineHom D.X.hom]
    [IsAffineHom U.X.hom] (hS : IsSplitTorus S.toGrp) (ha : a ≠ 0) {m : ℕ}
    {e : ∀ T : Over (Spec (CommRingCat.of k)),
      (T ⟶ U.X) ≃* Multiplicative (Fin m → Γ(T.left, ⊤))}
    (he : IsWeightVectorCoordinates (subgroupAction i a j hj) a e) :
    IsLinearVectorCoordinates (rootActionOfFixesTorus b i hfix a j hj) e :=
  isLinearVectorCoordinates_of_commute hS ha he
    (fun _ z t g => rootActionOfFixesTorus_commute b hfix hj z t g)

end Actions

section Quotient

variable {k : Type u} [Field k] {S : CommGroupScheme (Spec (CommRingCat.of k))}
    {G U U₂ D : GroupScheme (Spec (CommRingCat.of k))}
    {i : S.toGrp ⟶ G} {a : characterLattice S}
    {j : U ⟶ G} {hj : (subgroup i a).IsRepresentedBy j}
    {j₂ : U₂ ⟶ G} {hj₂ : (subgroup i (2 • a)).IsRepresentedBy j₂}
    (C : DoubleRootCommutatorPairing i a hj hj₂)
    (b : AutomorphicAction D G)
    (hfix : ∀ (T : Over (Spec (CommRingCat.of k))) (z : T ⟶ D.X) (t : T ⟶ S.X),
      b.act z (t ≫ i.hom.hom) = t ≫ i.hom.hom)

namespace DoubleRootCommutatorPairing

omit C in
/-- The action on the root group preserves the doubled root group. -/
theorem rootActionOfFixesTorus_isStable_double :
    (rootActionOfFixesTorus b i hfix a j hj).IsStable ((subgroup i (2 • a)).comap j) := by
  intro T z g hg
  rw [SubgroupFunctor.mem_comap] at hg ⊢
  rw [rootActionOfFixesTorus_act_comp]
  exact subgroup_isStable_of_fixes_torus b i hfix (2 • a) T z _ hg

/-- The induced action on the quotient of the root group by the doubled root group. -/
def torusQuotientAction : AutomorphicAction D C.V :=
  letI := C.quasiCompact
  C.isFppfQuotient.action (rootActionOfFixesTorus b i hfix a j hj)
    (rootActionOfFixesTorus_isStable_double b hfix)

/-- The quotient map intertwines the actions on the root group and on the quotient. -/
theorem torusQuotientAction_act_comp {T : Over (Spec (CommRingCat.of k))} (z : T ⟶ D.X)
    (g : T ⟶ U.X) :
    (C.torusQuotientAction b hfix).act z (g ≫ C.q.hom.hom) =
      (rootActionOfFixesTorus b i hfix a j hj).act z g ≫ C.q.hom.hom :=
  letI := C.quasiCompact
  C.isFppfQuotient.action_act _ _ z g

/-- Equality of maps out of a test scheme can be checked after locally lifting a point of the
quotient to the root group. -/
theorem hom_ext_of_local_lift {T Y : Over (Spec (CommRingCat.of k))} (x : T ⟶ C.V.X)
    (f f' : T ⟶ Y)
    (he : ∀ (W : Over (Spec (CommRingCat.of k))) (c : W ⟶ T) (g : W ⟶ U.X),
      c ≫ x = g ≫ C.q.hom.hom → c ≫ f = c ≫ f') : f = f' :=
  letI := C.quasiCompact
  letI : Flat C.q.hom.hom.left := C.isFppfQuotient.1
  letI : Surjective C.q.hom.hom.left := C.isFppfQuotient.2.1
  AutomorphicAction.hom_ext_of_local_quotient_lift C.q x f f' he

/-- The actions of `D` and of the split torus on the quotient commute. -/
theorem torusQuotientAction_commute {T : Over (Spec (CommRingCat.of k))} (z : T ⟶ D.X)
    (t : T ⟶ S.X) (x : T ⟶ C.V.X) :
    (C.torusQuotientAction b hfix).act z (C.action.act t x) =
      C.action.act t ((C.torusQuotientAction b hfix).act z x) := by
  apply C.hom_ext_of_local_lift x
  intro W c g hg
  rw [AutomorphicAction.naturality, AutomorphicAction.naturality, AutomorphicAction.naturality,
    AutomorphicAction.naturality, hg, C.act_comp, torusQuotientAction_act_comp,
    torusQuotientAction_act_comp, C.act_comp, rootActionOfFixesTorus_commute]

/-- If the torus action factors through `D`, the two actions on the quotient agree. -/
theorem action_eq_torusQuotientAction (s : S.toGrp ⟶ D)
    (hs : ∀ (T : Over (Spec (CommRingCat.of k))) (t : T ⟶ S.X) (g : T ⟶ G.X),
      b.act (t ≫ s.hom.hom) g = (t ≫ i.hom.hom) * g * (t ≫ i.hom.hom)⁻¹)
    {T : Over (Spec (CommRingCat.of k))} (t : T ⟶ S.X) (x : T ⟶ C.V.X) :
    C.action.act t x = (C.torusQuotientAction b hfix).act (t ≫ s.hom.hom) x := by
  apply C.hom_ext_of_local_lift x
  intro W c g hg
  rw [AutomorphicAction.naturality, AutomorphicAction.naturality, hg, C.act_comp,
    ← Category.assoc, torusQuotientAction_act_comp,
    subgroupAction_eq_rootActionOfFixesTorus b hfix hj s hs]

/-- **Linearity.** An affine group fixing the torus acts linearly in weight vector coordinates
on the quotient. -/
theorem isLinearVectorCoordinates_torusQuotientAction [IsAffineHom D.X.hom]
    [IsAffineHom C.V.X.hom] (hS : IsSplitTorus S.toGrp) (ha : a ≠ 0) {d : ℕ}
    {e : ∀ T : Over (Spec (CommRingCat.of k)),
      (T ⟶ C.V.X) ≃* Multiplicative (Fin d → Γ(T.left, ⊤))}
    (he : IsWeightVectorCoordinates C.action a e) :
    IsLinearVectorCoordinates (C.torusQuotientAction b hfix) e :=
  isLinearVectorCoordinates_of_commute hS ha he
    (fun _ z t x => C.torusQuotientAction_commute b hfix z t x)

end DoubleRootCommutatorPairing

end Quotient

section NormalForm

variable {k : Type u} [Field k] {S : CommGroupScheme (Spec (CommRingCat.of k))}
    {G U U₂ D : GroupScheme (Spec (CommRingCat.of k))}
    {i : S.toGrp ⟶ G} {a : characterLattice S}
    {j : U ⟶ G} {hj : (subgroup i a).IsRepresentedBy j}
    {j₂ : U₂ ⟶ G} {hj₂ : (subgroup i (2 • a)).IsRepresentedBy j₂}

/-- A Heisenberg normal form whose section is moreover equivariant for a group `D` acting on
`G` and fixing the split torus. -/
structure EquivariantHeisenbergNormalForm (C : DoubleRootCommutatorPairing i a hj hj₂)
    (b : AutomorphicAction D G)
    (hfix : ∀ (T : Over (Spec (CommRingCat.of k))) (z : T ⟶ D.X) (t : T ⟶ S.X),
      b.act z (t ≫ i.hom.hom) = t ≫ i.hom.hom)
    extends HeisenbergNormalForm C where
  act_sec_torus : ∀ (T : Over (Spec (CommRingCat.of k))) (z : T ⟶ D.X) (x : T ⟶ C.V.X),
    (rootActionOfFixesTorus b i hfix a j hj).act z (x ≫ sec) =
      (C.torusQuotientAction b hfix).act z x ≫ sec

namespace EquivariantHeisenbergNormalForm

variable {C : DoubleRootCommutatorPairing i a hj hj₂} {b : AutomorphicAction D G}
    {hfix : ∀ (T : Over (Spec (CommRingCat.of k))) (z : T ⟶ D.X) (t : T ⟶ S.X),
      b.act z (t ≫ i.hom.hom) = t ≫ i.hom.hom}
    (N : EquivariantHeisenbergNormalForm C b hfix)

/-- The inclusion of the doubled root group intertwines the actions of `D`. -/
theorem act_inclusion_torus {T : Over (Spec (CommRingCat.of k))} (z : T ⟶ D.X)
    (w : T ⟶ U₂.X) :
    (rootActionOfFixesTorus b i hfix a j hj).act z (w ≫ N.inclusion.hom.hom) =
      (rootActionOfFixesTorus b i hfix (2 • a) j₂ hj₂).act z w ≫ N.inclusion.hom.hom := by
  let : Mono j.hom.hom := hj.1
  apply (cancel_mono j.hom.hom).mp
  rw [rootActionOfFixesTorus_act_comp, Category.assoc, Category.assoc,
    N.inclusion_comp_hom, rootActionOfFixesTorus_act_comp]

/-- The cocycle intertwines the actions of `D` on the quotient and on the doubled root
group. -/
theorem cocycle_act_torus {T : Over (Spec (CommRingCat.of k))} (z : T ⟶ D.X)
    (x y : T ⟶ C.V.X) :
    lift ((C.torusQuotientAction b hfix).act z x) ((C.torusQuotientAction b hfix).act z y) ≫
        N.cocycle =
      (rootActionOfFixesTorus b i hfix (2 • a) j₂ hj₂).act z (lift x y ≫ N.cocycle) := by
  let := N.mono_inclusion
  apply (cancel_mono N.inclusion.hom.hom).mp
  rw [← N.act_inclusion_torus, N.cocycle_comp, N.cocycle_comp, AutomorphicAction.act_mul_right,
    AutomorphicAction.act_mul_right, AutomorphicAction.act_inv, N.act_sec_torus,
    N.act_sec_torus, N.act_sec_torus, AutomorphicAction.act_mul_right]

include N in
/-- The commutator pairing intertwines the actions of `D`. -/
theorem pairing_act_torus {T : Over (Spec (CommRingCat.of k))} (z : T ⟶ D.X)
    (x y : T ⟶ C.V.X) :
    lift ((C.torusQuotientAction b hfix).act z x) ((C.torusQuotientAction b hfix).act z y) ≫
        C.pairing =
      (rootActionOfFixesTorus b i hfix (2 • a) j₂ hj₂).act z (lift x y ≫ C.pairing) := by
  rw [N.pairing_eq, N.pairing_eq x y, N.cocycle_act_torus, N.cocycle_act_torus,
    AutomorphicAction.act_mul_right, AutomorphicAction.act_inv]

end EquivariantHeisenbergNormalForm

/-- **Existence of a torus-equivariant Heisenberg normal form.** Let `a` be a multipliable
relative root whose multiples `n • a`, `n ≥ 3`, are not relative roots, and let a torus `D`
act on `G`, fixing the split torus `S`, such that the action of `S` by conjugation factors
through a homomorphism `S ⟶ D`. Then the Heisenberg normal form can be chosen with a section
equivariant for `D`. -/
theorem nonempty_equivariantHeisenbergNormalForm [IsAffineHom G.X.hom] [Smooth G.X.hom]
    [IsAffineHom U.X.hom] (C : DoubleRootCommutatorPairing i a hj hj₂)
    (hS : IsSplitTorus S.toGrp) (ha : a ≠ 0)
    (hhigh : ∀ n : ℕ, 3 ≤ n → n • a ∉ relativeRoots i)
    (hD : IsTorus D) (b : AutomorphicAction D G)
    (hfix : ∀ (T : Over (Spec (CommRingCat.of k))) (z : T ⟶ D.X) (t : T ⟶ S.X),
      b.act z (t ≫ i.hom.hom) = t ≫ i.hom.hom)
    (s : S.toGrp ⟶ D)
    (hs : ∀ (T : Over (Spec (CommRingCat.of k))) (t : T ⟶ S.X) (g : T ⟶ G.X),
      b.act (t ≫ s.hom.hom) g = (t ≫ i.hom.hom) * g * (t ≫ i.hom.hom)⁻¹) :
    Nonempty (EquivariantHeisenbergNormalForm C b hfix) := by
  let : Mono j.hom.hom := hj.1
  have : IsAffine D.X.left := SplittingAssembly.isAffine_of_isTorus D hD
  have : IsAffineHom D.X.hom := inferInstance
  have hle : subgroup i (2 • a) ≤ subgroup i a :=
    double_subgroup_le_of_cyclicComparison cyclicRootFunctorComparison inferInstance hS i ha
  let n := hj.factorHom j₂ (by rw [hj₂.2]; exact hle)
  have hκ' := SubgroupFunctor.IsRepresentedBy.factor hj hj₂ hle
  have hn_comp : n ≫ j = j₂ := hj.factorHom_comp j₂ _
  let : Mono n.hom.hom := hκ'.1
  have hrange : SubgroupFunctor.range n = SubgroupFunctor.range (kernelι C.q) :=
    hκ'.2.trans C.isFppfQuotient.2.2.2.symm
  obtain ⟨d, e, he⟩ := C.weightVectorStructure.1
  have h2a : 2 • a ≠ 0 := hS.nsmul_ne_zero ha (by omega)
  obtain ⟨m, e', he'⟩ := weightVectorCoordinatesOfNoHigherRoots hS i h2a
    (hasNoHigherRoots_two_nsmul hhigh) hj₂
  have hV₂ : IsVectorGroupOfDimension U₂ m := ⟨e', he'.1⟩
  let : IsAffineHom C.V.X.hom := IsVectorGroupOfDimension.isAffineHom ⟨e, he.1⟩
  let : IsAffineHom U₂.X.hom := hV₂.isAffineHom
  let : Flat C.q.hom.hom.left := C.isFppfQuotient.1
  let : Surjective C.q.hom.hom.left := C.isFppfQuotient.2.1
  obtain ⟨s₀, hs₀⟩ := IsVectorGroupOfDimension.exists_quotientSection n C.q hrange hV₂
  have hker : ∀ (T : Over (Spec (CommRingCat.of k))) (g : T ⟶ U.X),
      g ∈ (SubgroupFunctor.range n).carrier T ↔ g ≫ C.q.hom.hom = 1 := by
    intro T g
    rw [hrange, mem_range_kernelι_iff]
  let cU := rootActionOfFixesTorus b i hfix a j hj
  let cU₂ := rootActionOfFixesTorus b i hfix (2 • a) j₂ hj₂
  let cV := C.torusQuotientAction b hfix
  have hq : ∀ (T : Over (Spec (CommRingCat.of k))) (z : T ⟶ D.X) (g : T ⟶ U.X),
      cU.act z g ≫ C.q.hom.hom = cV.act z (g ≫ C.q.hom.hom) :=
    fun T z g => (C.torusQuotientAction_act_comp b hfix z g).symm
  have hκj : n.hom.hom ≫ j.hom.hom = j₂.hom.hom := congrArg (fun f => f.hom.hom) hn_comp
  have hi : ∀ (T : Over (Spec (CommRingCat.of k))) (z : T ⟶ D.X) (w : T ⟶ U₂.X),
      cU.act z (w ≫ n.hom.hom) = cU₂.act z w ≫ n.hom.hom := by
    intro T z w
    apply (cancel_mono j.hom.hom).mp
    rw [rootActionOfFixesTorus_act_comp, Category.assoc, Category.assoc, hκj,
      rootActionOfFixesTorus_act_comp]
  have he'lin : IsLinearVectorCoordinates cU₂ e' :=
    isLinearVectorCoordinates_rootActionOfFixesTorus b hfix hj₂ hS h2a he'
  obtain ⟨σ, hσ, hσact⟩ := hD.exists_equivariantSection cU cV cU₂ n C.q hker hq hi s₀ hs₀ e'
    he'lin
  -- normalize the section at the identity
  let σ' : C.V.X ⟶ U.X := σ * ((1 : C.V.X ⟶ C.V.X) ≫ σ)⁻¹
  have hσ'pt (T : Over (Spec (CommRingCat.of k))) (x : T ⟶ C.V.X) :
      x ≫ σ' = (x ≫ σ) * ((1 : T ⟶ C.V.X) ≫ σ)⁻¹ := by
    rw [MonObj.comp_mul, GrpObj.comp_inv, ← Category.assoc, MonObj.comp_one]
  have hσ'q : σ' ≫ C.q.hom.hom = 𝟙 C.V.X := by
    rw [MonObj.mul_comp, GrpObj.inv_comp, hσ, Category.assoc, hσ, Category.comp_id, inv_one,
      mul_one]
  have hσ'one (T : Over (Spec (CommRingCat.of k))) : (1 : T ⟶ C.V.X) ≫ σ' = 1 := by
    rw [hσ'pt, mul_inv_cancel]
  have hσ'act (T : Over (Spec (CommRingCat.of k))) (z : T ⟶ D.X) (x : T ⟶ C.V.X) :
      cU.act z (x ≫ σ') = cV.act z x ≫ σ' := by
    rw [hσ'pt, hσ'pt, AutomorphicAction.act_mul_right, AutomorphicAction.act_inv, hσact,
      hσact, AutomorphicAction.act_one]
  have hσ'S (T : Over (Spec (CommRingCat.of k))) (t : T ⟶ S.X) (x : T ⟶ C.V.X) :
      (subgroupAction i a j hj).act t (x ≫ σ') = C.action.act t x ≫ σ' := by
    rw [subgroupAction_eq_rootActionOfFixesTorus b hfix hj s hs, hσ'act,
      C.action_eq_torusQuotientAction b hfix s hs]
  -- the cocycle on the universal pair
  let Δ : C.V.X ⊗ C.V.X ⟶ U.X :=
    (fst C.V.X C.V.X ≫ σ') * (snd C.V.X C.V.X ≫ σ') *
      ((fst C.V.X C.V.X * snd C.V.X C.V.X) ≫ σ')⁻¹
  have hΔ : Δ ∈ (SubgroupFunctor.range n).carrier (C.V.X ⊗ C.V.X) := by
    rw [hker]
    simp only [Δ, MonObj.mul_comp, GrpObj.inv_comp, Category.assoc, hσ'q, Category.comp_id,
      mul_inv_cancel]
  let β : C.V.X ⊗ C.V.X ⟶ U₂.X := Classical.choose hΔ
  have hβ : β ≫ n.hom.hom = Δ := Classical.choose_spec hΔ
  refine ⟨{
    inclusion := n
    inclusion_comp := hn_comp
    range_inclusion := hrange
    sec := σ'
    sec_comp := hσ'q
    one_sec := hσ'one
    act_sec := hσ'S
    cocycle := β
    sec_mul := fun T x y => ?_
    act_sec_torus := hσ'act }⟩
  have hβ' : (lift x y ≫ β) ≫ n.hom.hom = (x ≫ σ') * (y ≫ σ') * ((x * y) ≫ σ')⁻¹ := by
    rw [Category.assoc, hβ]
    simp only [Δ, MonObj.comp_mul, GrpObj.comp_inv, ← Category.assoc, lift_fst, lift_snd]
  rw [hβ']
  group

/-- A chosen torus-equivariant Heisenberg normal form. -/
def equivariantHeisenbergNormalForm [IsAffineHom G.X.hom] [Smooth G.X.hom]
    [IsAffineHom U.X.hom] (C : DoubleRootCommutatorPairing i a hj hj₂)
    (hS : IsSplitTorus S.toGrp) (ha : a ≠ 0)
    (hhigh : ∀ n : ℕ, 3 ≤ n → n • a ∉ relativeRoots i)
    (hD : IsTorus D) (b : AutomorphicAction D G)
    (hfix : ∀ (T : Over (Spec (CommRingCat.of k))) (z : T ⟶ D.X) (t : T ⟶ S.X),
      b.act z (t ≫ i.hom.hom) = t ≫ i.hom.hom)
    (s : S.toGrp ⟶ D)
    (hs : ∀ (T : Over (Spec (CommRingCat.of k))) (t : T ⟶ S.X) (g : T ⟶ G.X),
      b.act (t ≫ s.hom.hom) g = (t ≫ i.hom.hom) * g * (t ≫ i.hom.hom)⁻¹) :
    EquivariantHeisenbergNormalForm C b hfix :=
  Classical.choice (nonempty_equivariantHeisenbergNormalForm C hS ha hhigh hD b hfix s hs)

end NormalForm

end Langlands.GroupScheme.RelativeRoot
