import Langlands.GroupScheme.AutomorphicAction.Cocycles
import Langlands.GroupScheme.QuotientAction

/-! # Exactness for actual nonabelian cocycles -/

noncomputable section

universe u

open CategoryTheory CategoryTheory.MonoidalCategory
  CategoryTheory.CartesianMonoidalCategory AlgebraicGeometry
open scoped CategoryTheory.MonObj

namespace Langlands.GroupScheme.AutomorphicAction.Cocycle

variable {S : Scheme.{u}} {H N G Q : GroupScheme S}
    {aN : AutomorphicAction H N} {a : AutomorphicAction H G}
    {aQ : AutomorphicAction H Q} {T : Over S}

/-- Push an actual cocycle through an equivariant group homomorphism. -/
def map (q : G ⟶ Q) (hq : a.IsEquivariant aQ q) (c : a.Cocycle T) :
    aQ.Cocycle T where
  hom := c.hom ≫ q.hom.hom
  one b := by rw [← Category.assoc, c.one, MonObj.one_comp]
  mul b h h' := by
    rw [← Category.assoc, c.mul, MonObj.mul_comp, hq]
    rfl

@[simp]
theorem eval_map (q : G ⟶ Q) (hq : a.IsEquivariant aQ q)
    (c : a.Cocycle T) {V : Over S} (b : V ⟶ T) (h : V ⟶ H.X) :
    (c.map q hq).eval b h = c.eval b h ≫ q.hom.hom := by
  simp only [eval, map, Category.assoc]

@[simp]
theorem map_trivial (q : G ⟶ Q) (hq : a.IsEquivariant aQ q) :
    (trivial T : a.Cocycle T).map q hq = trivial T := by
  apply eval_ext
  intro V b h
  simp only [eval_map, eval_trivial, MonObj.one_comp]

theorem map_conjugate (q : G ⟶ Q) (hq : a.IsEquivariant aQ q)
    (g : T ⟶ G.X) (c : a.Cocycle T) :
    (conjugate g c).map q hq = conjugate (g ≫ q.hom.hom) (c.map q hq) := by
  apply eval_ext
  intro V b h
  simp only [eval_map, eval_conjugate, MonObj.mul_comp, AutomorphicAction.act_inv,
    GrpObj.inv_comp, Category.assoc]
  rw [hq h (b ≫ g), Category.assoc]

@[simp]
theorem map_coboundary (q : G ⟶ Q) (hq : a.IsEquivariant aQ q)
    (g : T ⟶ G.X) :
    (a.coboundary g).map q hq = aQ.coboundary (g ≫ q.hom.hom) := by
  rw [AutomorphicAction.coboundary, map_conjugate, map_trivial]
  rfl

theorem conjugate_coboundary (g g' : T ⟶ G.X) :
    conjugate g (a.coboundary g') = a.coboundary (g * g') :=
  (conjugate_mul g g' (trivial T)).symm

theorem conjugate_inv_conjugate (g : T ⟶ G.X) (c : a.Cocycle T) :
    conjugate g⁻¹ (conjugate g c) = c := by
  rw [← conjugate_mul, inv_mul_cancel, conjugate_one]

theorem conjugate_conjugate_inv (g : T ⟶ G.X) (c : a.Cocycle T) :
    conjugate g (conjugate g⁻¹ c) = c := by
  rw [← conjugate_mul, mul_inv_cancel, conjugate_one]

variable (n : N ⟶ G) (hn : aN.IsEquivariant a n) [Mono n.hom.hom]
    (c : a.Cocycle T)

/-- Factor an actual cocycle morphism through a represented invariant subgroup. -/
def lift (hc : c.hom ∈ (SubgroupFunctor.range n).carrier (T ⊗ H.X)) :
    aN.Cocycle T where
  hom := Classical.choose (SubgroupFunctor.mem_range.1 hc)
  one b := by
    apply (cancel_mono n.hom.hom).1
    rw [Category.assoc, Classical.choose_spec (SubgroupFunctor.mem_range.1 hc),
      c.one, MonObj.one_comp]
  mul b h h' := by
    apply (cancel_mono n.hom.hom).1
    rw [Category.assoc, Classical.choose_spec (SubgroupFunctor.mem_range.1 hc),
      c.mul, MonObj.mul_comp, hn]
    simp only [Category.assoc,
      Classical.choose_spec (SubgroupFunctor.mem_range.1 hc)]

@[simp]
theorem lift_map (hc : c.hom ∈ (SubgroupFunctor.range n).carrier (T ⊗ H.X)) :
    (c.lift n hn hc).map n hn = c := by
  apply ext
  exact Classical.choose_spec (SubgroupFunctor.mem_range.1 hc)

theorem lift_unique (hc : c.hom ∈ (SubgroupFunctor.range n).carrier (T ⊗ H.X))
    (d : aN.Cocycle T) (hd : d.map n hn = c) :
    d = c.lift n hn hc := by
  apply ext
  apply (cancel_mono n.hom.hom).1
  exact (congrArg Cocycle.hom hd).trans
    (congrArg Cocycle.hom (lift_map n hn c hc)).symm

variable (q : G ⟶ Q) (hq : a.IsEquivariant aQ q)
    (hker : SubgroupFunctor.range n = SubgroupFunctor.range (kernelι q))

omit [Mono n.hom.hom] in
include hker in
theorem hom_mem_range_of_map_trivial (hc : c.map q hq = trivial T) :
    c.hom ∈ (SubgroupFunctor.range n).carrier (T ⊗ H.X) := by
  rw [hker, mem_range_kernelι_iff]
  exact congrArg Cocycle.hom hc

/-- A cocycle with trivial quotient is an actual cocycle of the represented
kernel, for its original induced action. -/
def kernelLift (hc : c.map q hq = trivial T) : aN.Cocycle T :=
  c.lift n hn (hom_mem_range_of_map_trivial n c q hq hker hc)

@[simp]
theorem kernelLift_map (hc : c.map q hq = trivial T) :
    (kernelLift n hn c q hq hker hc).map n hn = c :=
  lift_map n hn c _

include hn hq hker in
/-- Lift a specified quotient coboundary point and correct the residual kernel
cocycle. No commutativity, centrality, or surjectivity on all tests is required. -/
theorem exists_coboundary_of_map_eq_coboundary
    (g : T ⟶ G.X)
    (hc : c.map q hq = aQ.coboundary (g ≫ q.hom.hom))
    (hN : ∀ d : aN.Cocycle T, ∃ v : T ⟶ N.X, d = aN.coboundary v) :
    ∃ v : T ⟶ N.X, c = a.coboundary (g * (v ≫ n.hom.hom)) := by
  have htriv : (conjugate g⁻¹ c).map q hq = trivial T := by
    rw [map_conjugate, hc, GrpObj.inv_comp]
    exact conjugate_inv_conjugate (g ≫ q.hom.hom) (trivial T)
  let d := kernelLift n hn (conjugate g⁻¹ c) q hq hker htriv
  obtain ⟨v, hv⟩ := hN d
  have hd : conjugate g⁻¹ c = a.coboundary (v ≫ n.hom.hom) := by
    rw [← kernelLift_map n hn (conjugate g⁻¹ c) q hq hker htriv]
    change d.map n hn = _
    rw [hv, map_coboundary]
  refine ⟨v, ?_⟩
  have he := congrArg (conjugate g) hd
  rwa [conjugate_conjugate_inv, conjugate_coboundary] at he

end Langlands.GroupScheme.AutomorphicAction.Cocycle
