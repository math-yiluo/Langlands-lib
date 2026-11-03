import Langlands.GroupScheme.SubgroupFunctor
import Langlands.GroupScheme.FiniteFieldTorsorPointStatement
import Langlands.GroupScheme.SchemeActionOfPointLaws
import Langlands.AlgebraicGeometry.PointTopology.RationalPoints

/-! # Actual torsors given by the fibers of an exact coset quotient -/

noncomputable section

universe u

open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory
open CategoryTheory.CartesianMonoidalCategory AlgebraicGeometry
open Langlands.AlgebraicGeometry.PointTopology
open scoped CategoryTheory.MonObj

namespace Langlands.GroupScheme.Dynamic

variable {S : Scheme.{u}} (G : GroupScheme S) {Q : Over S} (q : G.X ⟶ Q)
variable (p : Over.mk (𝟙 S) ⟶ Q)

/-- The actual scheme fiber of a relative quotient at a section of its base. -/
def flagQuotientFiber : Over S :=
  Over.mk (pullback.snd q.left p.left)

/-- The fiber's actual map to the original group scheme. -/
def flagQuotientFiberι : flagQuotientFiber G q p ⟶ G.X :=
  Over.homMk (pullback.fst q.left p.left) (by
    change pullback.fst q.left p.left ≫ G.X.hom = pullback.snd q.left p.left
    rw [← Over.w q, ← Category.assoc, pullback.condition, Category.assoc, Over.w p]
    exact Category.comp_id _)

@[reassoc]
theorem flagQuotientFiberι_comp :
    flagQuotientFiberι G q p ≫ q = toUnit (flagQuotientFiber G q p) ≫ p :=
  Over.OverMorphism.ext pullback.condition

/-- A morphism into the fiber is determined by its group component. -/
theorem flagQuotientFiber_hom_ext {T : Over S}
    (x y : T ⟶ flagQuotientFiber G q p)
    (he : x ≫ flagQuotientFiberι G q p = y ≫ flagQuotientFiberι G q p) : x = y := by
  apply Over.OverMorphism.ext
  apply pullback.hom_ext
  · exact congrArg (fun f => f.left) he
  · exact (Over.w x).trans (Over.w y).symm

/-- The actual pullback lift of a group point mapping to the fixed quotient
section after restriction to its test scheme. -/
def flagQuotientFiberLift {T : Over S} (g : T ⟶ G.X)
    (hg : g ≫ q = toUnit T ≫ p) : T ⟶ flagQuotientFiber G q p :=
  Over.homMk
    (pullback.lift g.left T.hom (congrArg (fun f => f.left) hg))
    (pullback.lift_snd _ _ _)

@[reassoc]
theorem flagQuotientFiberLift_ι {T : Over S} (g : T ⟶ G.X)
    (hg : g ≫ q = toUnit T ≫ p) :
    flagQuotientFiberLift G q p g hg ≫ flagQuotientFiberι G q p = g :=
  Over.OverMorphism.ext (pullback.lift_fst _ _ _)

instance [Flat q.left] : Flat (flagQuotientFiber G q p).hom := by
  change Flat (pullback.snd q.left p.left)
  infer_instance

instance [Surjective q.left] : Surjective (flagQuotientFiber G q p).hom := by
  change Surjective (pullback.snd q.left p.left)
  infer_instance

instance [QuasiCompact q.left] : QuasiCompact (flagQuotientFiber G q p).hom := by
  change QuasiCompact (pullback.snd q.left p.left)
  infer_instance

variable (P : GroupScheme S) (i : P ⟶ G)
variable (hfib : ∀ (T : Over S) (g h : T ⟶ G.X),
  g ≫ q = h ≫ q ↔ g⁻¹ * h ∈ (SubgroupFunctor.range i).carrier T)

include hfib

/-- Right multiplication by an inverse subgroup point gives a left action on
the actual quotient fiber. -/
def flagQuotientFiberAct {T : Over S} (h : T ⟶ P.X)
    (x : T ⟶ flagQuotientFiber G q p) : T ⟶ flagQuotientFiber G q p :=
  flagQuotientFiberLift G q p
    ((x ≫ flagQuotientFiberι G q p) * (h ≫ i.hom.hom)⁻¹) (by
      have hm : h ≫ i.hom.hom ∈ (SubgroupFunctor.range i).carrier T := ⟨h, rfl⟩
      have he := (hfib T (x ≫ flagQuotientFiberι G q p)
        ((x ≫ flagQuotientFiberι G q p) * (h ≫ i.hom.hom)⁻¹)).mpr
        (by simpa only [inv_mul_cancel_left] using
          ((SubgroupFunctor.range i).carrier T).inv_mem hm)
      rw [← he, Category.assoc, flagQuotientFiberι_comp, comp_toUnit_assoc])

@[reassoc]
theorem flagQuotientFiberAct_ι {T : Over S} (h : T ⟶ P.X)
    (x : T ⟶ flagQuotientFiber G q p) :
    flagQuotientFiberAct G q p P i hfib h x ≫ flagQuotientFiberι G q p =
      (x ≫ flagQuotientFiberι G q p) * (h ≫ i.hom.hom)⁻¹ :=
  flagQuotientFiberLift_ι G q p _ _

theorem flagQuotientFiberAct_naturality {T V : Over S} (b : V ⟶ T)
    (h : T ⟶ P.X) (x : T ⟶ flagQuotientFiber G q p) :
    b ≫ flagQuotientFiberAct G q p P i hfib h x =
      flagQuotientFiberAct G q p P i hfib (b ≫ h) (b ≫ x) := by
  apply flagQuotientFiber_hom_ext G q p
  rw [Category.assoc, flagQuotientFiberAct_ι, flagQuotientFiberAct_ι,
    MonObj.comp_mul, GrpObj.comp_inv, Category.assoc, Category.assoc]

theorem flagQuotientFiberAct_one {T : Over S}
    (x : T ⟶ flagQuotientFiber G q p) :
    flagQuotientFiberAct G q p P i hfib 1 x = x := by
  apply flagQuotientFiber_hom_ext G q p
  rw [flagQuotientFiberAct_ι, MonObj.one_comp, inv_one, mul_one]

theorem flagQuotientFiberAct_mul {T : Over S} (h h' : T ⟶ P.X)
    (x : T ⟶ flagQuotientFiber G q p) :
    flagQuotientFiberAct G q p P i hfib (h * h') x =
      flagQuotientFiberAct G q p P i hfib h
        (flagQuotientFiberAct G q p P i hfib h' x) := by
  apply flagQuotientFiber_hom_ext G q p
  rw [flagQuotientFiberAct_ι, flagQuotientFiberAct_ι, flagQuotientFiberAct_ι,
    MonObj.mul_comp, mul_inv_rev, mul_assoc]

/-- One actual action morphism on the fiber, obtained by its universal test. -/
def flagQuotientFiberActionHom :
    P.X ⊗ flagQuotientFiber G q p ⟶ flagQuotientFiber G q p :=
  flagQuotientFiberAct G q p P i hfib (fst _ _) (snd _ _)

theorem comp_flagQuotientFiberActionHom {T : Over S} (h : T ⟶ P.X)
    (x : T ⟶ flagQuotientFiber G q p) :
    lift h x ≫ flagQuotientFiberActionHom G q p P i hfib =
      flagQuotientFiberAct G q p P i hfib h x := by
  rw [flagQuotientFiberActionHom, flagQuotientFiberAct_naturality, lift_fst, lift_snd]

/-- The standard lawful categorical left action on the actual fiber. -/
@[instance_reducible]
def flagQuotientFiberModObj : ModObj P.X (flagQuotientFiber G q p) :=
  schemeActionOfPointLaws (flagQuotientFiberActionHom G q p P i hfib)
    (fun x => by
      rw [comp_flagQuotientFiberActionHom, flagQuotientFiberAct_one])
    (fun h h' x => by
      rw [comp_flagQuotientFiberActionHom, comp_flagQuotientFiberActionHom,
        comp_flagQuotientFiberActionHom, flagQuotientFiberAct_mul])

/-- Exact coset fibers and a monic subgroup inclusion give simple transitivity
on every relative test scheme. -/
theorem flagQuotientFiber_simply_transitive [Mono i.hom.hom] :
    letI := flagQuotientFiberModObj G q p P i hfib
    ∀ (T : Over S) (x y : T ⟶ flagQuotientFiber G q p),
      ∃! (h : T ⟶ P.X), h • x = y := by
  let := flagQuotientFiberModObj G q p P i hfib
  have heval {T : Over S} (h : T ⟶ P.X)
      (x : T ⟶ flagQuotientFiber G q p) :
      (h • x) ≫ flagQuotientFiberι G q p =
        (x ≫ flagQuotientFiberι G q p) * (h ≫ i.hom.hom)⁻¹ := by
    change (lift h x ≫ flagQuotientFiberActionHom G q p P i hfib) ≫
      flagQuotientFiberι G q p = _
    rw [comp_flagQuotientFiberActionHom, flagQuotientFiberAct_ι]
  intro T x y
  have hxy : (y ≫ flagQuotientFiberι G q p) ≫ q =
      (x ≫ flagQuotientFiberι G q p) ≫ q := by
    rw [Category.assoc, Category.assoc, flagQuotientFiberι_comp,
      comp_toUnit_assoc, comp_toUnit_assoc]
  obtain ⟨h, hh⟩ := SubgroupFunctor.mem_range.mp
    ((hfib T (y ≫ flagQuotientFiberι G q p) (x ≫ flagQuotientFiberι G q p)).mp hxy)
  refine ⟨h, ?_, ?_⟩
  · apply flagQuotientFiber_hom_ext G q p
    rw [heval, hh, mul_inv_rev, inv_inv, mul_inv_cancel_left]
  · intro a ha
    apply (cancel_mono i.hom.hom).mp
    have ha₀ : (x ≫ flagQuotientFiberι G q p) * (a ≫ i.hom.hom)⁻¹ =
        y ≫ flagQuotientFiberι G q p := by
      simpa only [heval] using
        congrArg (fun z => z ≫ flagQuotientFiberι G q p) ha
    have he := congrArg
      (fun v : T ⟶ G.X => v⁻¹ * (x ≫ flagQuotientFiberι G q p)) ha₀
    have hai : a ≫ i.hom.hom =
        (y ≫ flagQuotientFiberι G q p)⁻¹ * (x ≫ flagQuotientFiberι G q p) := by
      simpa only [mul_inv_rev, inv_inv, mul_assoc, inv_mul_cancel, mul_one] using he
    exact hai.trans hh.symm

/-- The lawful action's actual categorical shear is an isomorphism. -/
theorem flagQuotientFiber_leftSMul_isIso [Mono i.hom.hom] :
    letI := flagQuotientFiberModObj G q p P i hfib
    IsIso (ModObj.leftSMul P.X (flagQuotientFiber G q p)) := by
  let := flagQuotientFiberModObj G q p P i hfib
  exact ModObj.isIso_leftSMul_iff.mpr
    (flagQuotientFiber_simply_transitive G q p P i hfib)

omit hfib

section FiniteField

variable (k : Type u) [Field k] [Finite k]
variable (Gₖ Pₖ : GroupScheme (Spec (CommRingCat.of k)))
variable {Qₖ : Over (Spec (CommRingCat.of k))} (qₖ : Gₖ.X ⟶ Qₖ) (iₖ : Pₖ ⟶ Gₖ)
variable [Mono iₖ.hom.hom] [Flat qₖ.left] [Surjective qₖ.left] [QuasiCompact qₖ.left]
variable (hfibₖ : ∀ (T : Over (Spec (CommRingCat.of k))) (g h : T ⟶ Gₖ.X),
  g ≫ qₖ = h ≫ qₖ ↔ g⁻¹ * h ∈ (SubgroupFunctor.range iₖ).carrier T)

include hfibₖ

/-- The finite-field torsor point proposition applies to the actual fibers of
this same quotient and gives rational lifts. -/
theorem rational_lifts_of_finite_torsor
    (hfinite : FiniteFieldTorsorPointStatement.{u})
    [Smooth Pₖ.X.hom] [IsAffineHom Pₖ.X.hom]
    (hP : ConnectedSpace Pₖ.X.left) :
    ∀ p : RingPoint k Qₖ k, ∃ g : RingPoint k Gₖ.X k, g ≫ qₖ = p := by
  intro p
  dsimp only [RingPoint] at p
  let p₀ : RationalPoint k Qₖ := (rationalPointEquiv k Qₖ).symm p
  let X := flagQuotientFiber Gₖ qₖ p₀
  let : ModObj Pₖ.X X := flagQuotientFiberModObj Gₖ qₖ p₀ Pₖ iₖ hfibₖ
  obtain ⟨x⟩ := hfinite k Pₖ hP X
    (inferInstance : Flat X.hom)
    (inferInstance : Surjective X.hom)
    (inferInstance : QuasiCompact X.hom)
    (flagQuotientFiber_leftSMul_isIso Gₖ qₖ p₀ Pₖ iₖ hfibₖ)
  let x₀ : RationalPoint k X := (rationalPointEquiv k X).symm x
  refine ⟨rationalPointEquiv k Gₖ.X (x₀ ≫ flagQuotientFiberι Gₖ qₖ p₀), ?_⟩
  rw [← rationalPointEquiv_natural]
  have hx : (x₀ ≫ flagQuotientFiberι Gₖ qₖ p₀) ≫ qₖ = p₀ := by
    rw [Category.assoc, flagQuotientFiberι_comp, ← Category.assoc]
    have ht : x₀ ≫ toUnit X = 𝟙 (Over.mk (𝟙 (Spec (CommRingCat.of k)))) :=
      toUnit_unique _ _
    rw [ht, Category.id_comp]
  rw [hx]
  exact Equiv.apply_symm_apply _ _

end FiniteField

end Langlands.GroupScheme.Dynamic
