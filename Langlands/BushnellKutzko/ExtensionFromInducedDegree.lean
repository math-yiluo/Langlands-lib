import Langlands.BushnellKutzko.ExtensionFromInducedDegreeStatement

/-! # Extracting an extension in the induced degree -/

noncomputable section

namespace Langlands.BushnellKutzko

open Representation

universe uG uV uW uX

variable {G : Type uG} [Group G]
  {V : Type uV} [AddCommGroup V] [Module ℂ V]
  {W : Type uW} [AddCommGroup W] [Module ℂ W]
  {X : Type uX} [AddCommGroup X] [Module ℂ X]
  {H K : Subgroup G} {ρ : Representation ℂ H V} {σ : Representation ℂ K X}
  {π : Representation ℂ G W}

/-- Projecting the translate of a subgroup map gives an intertwiner on the
common subgroup. -/
def projectedTranslate (i : ρ.IntertwiningMap (π.comp H.subtype))
    (p : IntertwiningMap (π.comp K.subtype) σ) (x : G) :
    intertwiningSpace ρ σ x :=
  ⟨p.toLinearMap ∘ₗ π x⁻¹ ∘ₗ i.toLinearMap, fun d => by
    apply LinearMap.ext
    intro v
    let a := intertwiningDomainConj H K x d
    let b := intertwiningDomainIncl H K x d
    change p (π x⁻¹ (i (ρ a v))) = σ b (p (π x⁻¹ (i v)))
    rw [i.isIntertwining, ← p.isIntertwining]
    change p (π x⁻¹ (π (x * (d : G) * x⁻¹) (i v))) =
      p (π (d : G) (π x⁻¹ (i v)))
    congr 1
    rw [← Module.End.mul_apply, ← map_mul, ← Module.End.mul_apply, ← map_mul]
    congr 2
    group⟩

@[simp] theorem projectedTranslate_apply (i : ρ.IntertwiningMap (π.comp H.subtype))
    (p : IntertwiningMap (π.comp K.subtype) σ) (x : G) (v : V) :
    projectedTranslate i p x v = p (π x⁻¹ (i v)) :=
  rfl

set_option maxHeartbeats 1000000 in
/-- If the induced degree is attained, a split copy of `ρ` whose self-intertwining
is contained in `A` is stable under `A`. Its extension to `A` coinduces to `π`.
Every copy of `ρ` in the restriction of `π` has image in that same subspace. -/
theorem extensionFromInducedDegree : ExtensionFromInducedDegreeStatement.{uG, uV, uW} := by
  intro G _ H A _ hHA V _ _ _ W _ _ _ ρ π i p hpi hsupport hdegree
  classical
  let Q := G ⧸ A
  let : Fintype Q := Fintype.ofFinite _
  let q₀ : Q := QuotientGroup.mk (1 : G)
  let t (q : Q) : G := if q = q₀ then 1 else q.out
  have ht₀ : t q₀ = 1 := ite_eq_left rfl
  have ht (q : Q) : (QuotientGroup.mk (t q) : Q) = q := by
    by_cases hq : q = q₀
    · simp [t, hq, q₀]
    · simp [t, hq]
  have ht_mem (q : Q) (hq : q ≠ q₀) : t q ∉ A := by
    intro h
    apply hq
    rw [← ht q]
    exact QuotientGroup.eq.mpr (by simpa using A.inv_mem h)
  have hzero (j : ρ.IntertwiningMap (π.comp H.subtype)) {g : G} (hg : g ∉ A) (v : V) :
      p (π g (j v)) = 0 := by
    have hz : projectedTranslate j p g⁻¹ = 0 := by
      by_contra hn
      exact hg (A.inv_mem_iff.mp (hsupport _ ⟨_, hn⟩))
    simpa using congrArg (fun f : intertwiningSpace ρ ρ g⁻¹ => f v) hz
  let component (q : Q) : W →ₗ[ℂ] V := p.toLinearMap ∘ₗ π (t q)⁻¹
  let assemble : (Q → V) →ₗ[ℂ] W :=
    ∑ q : Q, π (t q) ∘ₗ i.toLinearMap ∘ₗ LinearMap.proj q
  have hcomponent (f : Q → V) (q : Q) : component q (assemble f) = f q := by
    simp only [assemble, LinearMap.sum_apply, LinearMap.comp_apply, LinearMap.proj_apply,
      IntertwiningMap.toLinearMap_apply, map_sum]
    rw [Finset.sum_eq_single q]
    · change p (π (t q)⁻¹ (π (t q) (i (f q)))) = f q
      rw [π.inv_self_apply, hpi]
    · intro q' _ hne
      change p (π (t q)⁻¹ (π (t q') (i (f q')))) = 0
      rw [← Module.End.mul_apply, ← map_mul]
      exact hzero i (fun h => hne ((ht q').symm.trans
        ((QuotientGroup.eq.mpr h).symm.trans (ht q)))) (f q')
    · simp
  let coordinates : W →ₗ[ℂ] (Q → V) := LinearMap.pi component
  have hleft : Function.LeftInverse coordinates assemble := fun f => funext (hcomponent f)
  have hrank : Module.finrank ℂ (Q → V) = Module.finrank ℂ W := by
    rw [Module.finrank_pi_fintype, Finset.sum_const, Finset.card_univ, nsmul_eq_mul,
      ← Nat.card_eq_fintype_card, ← A.index_eq_card, hdegree]
    rfl
  let b := LinearEquiv.ofInjectiveOfFinrankEq assemble hleft.injective hrank
  have hright : Function.RightInverse coordinates assemble := by
    intro w
    obtain ⟨f, rfl⟩ := b.surjective w
    change assemble (coordinates (assemble f)) = assemble f
    rw [hleft]
  have hcoords := hright.injective
  have hcomp₀ (w : W) : component q₀ w = p w := by
    simp [component, ht₀]
  have hm (a : A) (v : V) : π a (i v) = i (p (π a (i v))) := by
    apply hcoords
    funext q
    change component q (π a (i v)) = component q (i (p (π a (i v))))
    by_cases hq : q = q₀
    · subst q
      simp only [hcomp₀, hpi]
    · change p (π (t q)⁻¹ (π a (i v))) = p (π (t q)⁻¹ (i (p (π a (i v)))))
      rw [← Module.End.mul_apply, ← map_mul,
        hzero i (fun h => ht_mem q hq (A.inv_mem_iff.mp ((A.mul_mem_cancel_right a.2).mp h))),
        hzero i (fun h => ht_mem q hq (A.inv_mem_iff.mp h))]
  let κ : Representation ℂ A V :=
    { toFun := fun a => p.toLinearMap ∘ₗ π a ∘ₗ i.toLinearMap
      map_one' := by
        ext v
        change p (π (1 : G) (i v)) = v
        rw [map_one, Module.End.one_apply, hpi]
      map_mul' := fun a a' => by
        ext v
        change p (π ((a : G) * a') (i v)) = p (π a (i (p (π a' (i v)))))
        rw [← hm, map_mul, Module.End.mul_apply] }
  have hk (a : A) (v : V) : κ a v = p (π a (i v)) := rfl
  have hincl : κ.comp (Subgroup.inclusion hHA) = ρ := by
    ext h v
    change p (π h (i v)) = ρ h v
    have hi : i (ρ h v) = π h (i v) := IntertwiningMap.isIntertwining _ _ i h v
    rw [← hi, hpi]
  have hp (a : A) (w : W) : p (π a w) = κ a (p w) := by
    obtain ⟨f, rfl⟩ := b.surjective w
    change p (π a (assemble f)) = κ a (p (assemble f))
    rw [← hcomp₀ (assemble f), hcomponent]
    simp only [assemble, LinearMap.sum_apply, LinearMap.comp_apply, LinearMap.proj_apply,
      IntertwiningMap.toLinearMap_apply, map_sum]
    rw [Finset.sum_eq_single q₀]
    · change p (π a (π (t q₀) (i (f q₀)))) = κ a (f q₀)
      rw [ht₀, map_one, Module.End.one_apply, hk]
    · intro q _ hq
      change p (π a (π (t q) (i (f q)))) = 0
      rw [← Module.End.mul_apply, ← map_mul]
      exact hzero i (fun h => ht_mem q hq ((A.mul_mem_cancel_left a.2).mp h)) (f q)
    · simp
  let F : π.IntertwiningMap (Representation.coind A.subtype κ) :=
    { toLinearMap :=
        { toFun := fun w => ⟨fun g => p (π g w), fun a g => by
            change p (π ((a : G) * g) w) = κ a (p (π g w))
            rw [map_mul, Module.End.mul_apply, hp]⟩
          map_add' := fun w w' => Subtype.ext (funext fun g => by simp)
          map_smul' := fun c w => Subtype.ext (funext fun g => by simp) }
      isIntertwining' := fun g => LinearMap.ext fun w => Subtype.ext (funext fun x => by
        change p (π x (π g w)) = p (π (x * g) w)
        rw [map_mul, Module.End.mul_apply]) }
  have hF (w : W) (g : G) : (F w).val g = p (π g w) := rfl
  have hbij : Function.Bijective F := by
    constructor
    · intro w w' h
      apply hcoords
      funext q
      exact congrArg (fun z : Representation.coindV A.subtype κ => z.val (t q)⁻¹) h
    · intro f
      let v (q : Q) := f.val (t q)⁻¹
      refine ⟨assemble v, Subtype.ext (funext fun g => ?_)⟩
      let q : Q := QuotientGroup.mk g⁻¹
      let a : A := ⟨g * t q, by simpa only [inv_inv] using QuotientGroup.eq.mp (ht q).symm⟩
      have ha : g = (a : G) * (t q)⁻¹ := by dsimp [a]; group
      have hv : p (π (t q)⁻¹ (assemble v)) = f.val (t q)⁻¹ := hcomponent v q
      rw [hF, ha, map_mul, Module.End.mul_apply, hp, hv]
      exact (f.2 a (t q)⁻¹).symm
  refine ⟨κ, hincl, ⟨F.ofBijective hbij⟩, fun j v => ?_⟩
  apply hcoords
  funext q
  change component q (j v) = component q (i (p (j v)))
  by_cases hq : q = q₀
  · subst q
    simp only [hcomp₀, hpi]
  · have hq' : (t q)⁻¹ ∉ A := fun h => ht_mem q hq (A.inv_mem_iff.mp h)
    change p (π (t q)⁻¹ (j v)) = p (π (t q)⁻¹ (i (p (j v))))
    rw [hzero j hq', hzero i hq']

end Langlands.BushnellKutzko
