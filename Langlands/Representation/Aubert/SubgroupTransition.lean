import Langlands.Representation.Jacquet.LocalizationTransition
import Langlands.Representation.Induction.Definitions

/-!
# Pointwise transitions in the induction--coinvariant function model

All subgroups are actual subgroups of the ambient group. The coefficient action
is the unnormalized quotient action. Comparison with normalized parabolic
induction of normalized Jacquet restriction is a separate normalization step.
-/

noncomputable section

set_option maxHeartbeats 1600000

namespace Langlands.Aubert.SubgroupTransition

open Jacquet.Localization

universe uR uG uV uW

variable {R : Type uR} {G : Type uG} [CommRing R] [Group G]
variable [TopologicalSpace G] [IsTopologicalGroup G]
variable {V : Type uV} {W : Type uW}
variable [AddCommGroup V] [Module R V] [AddCommGroup W] [Module R W]

/-- The actual quotient action of `P` on the trivial-character `U`-coinvariants. -/
abbrev inducing (P U : Subgroup G) (hPU : P ≤ Subgroup.normalizer U)
    (ρ : Representation R G V) :=
  action ρ U 1 P hPU (isInvariant_one U P hPU)

/-- The actual smooth induction of this quotient action. -/
abbrev term (P U : Subgroup G) (hPU : P ≤ Subgroup.normalizer U)
    (ρ : Representation R G V) :=
  Induction.smoothInduced P (inducing P U hPU ρ)

/-- The pointwise quotient map on all covariant functions. -/
def fullMap (P U Q N : Subgroup G) (hPU : P ≤ Subgroup.normalizer U)
    (hQN : Q ≤ Subgroup.normalizer N) (hQP : Q ≤ P) (hUN : U ≤ N)
    (ρ : Representation R G V) :
    (Induction.equivariantAction P (inducing P U hPU ρ)).IntertwiningMap
      (Induction.equivariantAction Q (inducing Q N hQN ρ)) where
  toLinearMap :=
    { toFun := fun f => ⟨fun g => transitionLinear U N hUN 1 1 (fun _ => rfl) ρ (f.1 g), by
        intro q g
        have hf := f.property (Subgroup.inclusion hQP q) g
        change f.1 ((q : G) * g) =
          inducing P U hPU ρ (Subgroup.inclusion hQP q) (f.1 g) at hf
        change transitionLinear U N hUN 1 1 (fun _ => rfl) ρ (f.1 ((q : G) * g)) =
          inducing Q N hQN ρ q
            (transitionLinear U N hUN 1 1 (fun _ => rfl) ρ (f.1 g))
        rw [hf]
        obtain ⟨v, hv⟩ := mk_surjective ρ U (1 : U →* Rˣ) (f.1 g)
        rw [← hv]
        rfl⟩
      map_add' f f' := by
        ext g
        exact (transitionLinear U N hUN 1 1 (fun _ => rfl) ρ).map_add _ _
      map_smul' a f := by
        ext g
        exact (transitionLinear U N hUN 1 1 (fun _ => rfl) ρ).map_smul _ _ }
  isIntertwining' _ := by
    ext f x
    rfl

/-- The same pointwise map restricted to actual smooth vectors. -/
def map (P U Q N : Subgroup G) (hPU : P ≤ Subgroup.normalizer U)
    (hQN : Q ≤ Subgroup.normalizer N) (hQP : Q ≤ P) (hUN : U ≤ N)
    (ρ : Representation R G V) :
    (term P U hPU ρ).IntertwiningMap (term Q N hQN ρ) :=
  smoothMap (fullMap P U Q N hPU hQN hQP hUN ρ)

@[simp]
theorem map_eval (P U Q N : Subgroup G) (hPU : P ≤ Subgroup.normalizer U)
    (hQN : Q ≤ Subgroup.normalizer N) (hQP : Q ≤ P) (hUN : U ≤ N)
    (ρ : Representation R G V)
    (f : Induction.SmoothFunctions P (inducing P U hPU ρ)) (g : G) :
    Induction.eval Q (inducing Q N hQN ρ) (map P U Q N hPU hQN hQP hUN ρ f) g =
      transitionLinear U N hUN 1 1 (fun _ => rfl) ρ
        (Induction.eval P (inducing P U hPU ρ) f g) := rfl

@[simp]
theorem map_refl (P U : Subgroup G) (hPU : P ≤ Subgroup.normalizer U)
    (ρ : Representation R G V) :
    map P U P U hPU hPU le_rfl le_rfl ρ =
      Representation.IntertwiningMap.id (term P U hPU ρ) := by
  ext f g
  exact LinearMap.congr_fun (transitionLinear_refl U 1 ρ)
    (Induction.eval P (inducing P U hPU ρ) f g)

/-- The actual function maps compose for every chain of the subgroup containments. -/
theorem map_comp (P U Q N T H : Subgroup G)
    (hPU : P ≤ Subgroup.normalizer U) (hQN : Q ≤ Subgroup.normalizer N)
    (hTH : T ≤ Subgroup.normalizer H)
    (hQP : Q ≤ P) (hUN : U ≤ N) (hTQ : T ≤ Q) (hNH : N ≤ H)
    (ρ : Representation R G V) :
    (map Q N T H hQN hTH hTQ hNH ρ).comp (map P U Q N hPU hQN hQP hUN ρ) =
      map P U T H hPU hTH (hTQ.trans hQP) (hUN.trans hNH) ρ := by
  ext f g
  exact LinearMap.congr_fun
    (transitionLinear_comp U N H hUN hNH 1 1 1 (fun _ => rfl) (fun _ => rfl) ρ)
    (Induction.eval P (inducing P U hPU ρ) f g)

/-- The termwise map induced by an ambient intertwiner. -/
def termMap (P U : Subgroup G) (hPU : P ≤ Subgroup.normalizer U)
    {ρ : Representation R G V} {σ : Representation R G W} (f : ρ.IntertwiningMap σ) :
    (term P U hPU ρ).IntertwiningMap (term P U hPU σ) :=
  Induction.smoothInducedMap P
    (Jacquet.Localization.map U 1 P hPU (isInvariant_one U P hPU) f)

/-- Naturality of the canonical transitions in the ambient representation. -/
theorem map_natural (P U Q N : Subgroup G) (hPU : P ≤ Subgroup.normalizer U)
    (hQN : Q ≤ Subgroup.normalizer N) (hQP : Q ≤ P) (hUN : U ≤ N)
    {ρ : Representation R G V} {σ : Representation R G W} (f : ρ.IntertwiningMap σ) :
    (map P U Q N hPU hQN hQP hUN σ).comp (termMap P U hPU f) =
      (termMap Q N hQN f).comp (map P U Q N hPU hQN hQP hUN ρ) := by
  ext x g
  exact LinearMap.congr_fun
    (transitionLinear_natural U N hUN 1 1 (fun _ => rfl) f)
    (Induction.eval P (inducing P U hPU ρ) x g)

/-- The canonical orbit-function map before imposing smoothness. -/
def fullAugmentation (P U : Subgroup G) (hPU : P ≤ Subgroup.normalizer U)
    (ρ : Representation R G V) :
    ρ.IntertwiningMap (Induction.equivariantAction P (inducing P U hPU ρ)) where
  toLinearMap :=
    { toFun := fun v => ⟨fun g => mk ρ U 1 (ρ g v), by
        intro p g
        change mk ρ U 1 (ρ ((p : G) * g) v) = mk ρ U 1 (ρ p (ρ g v))
        rw [map_mul]
        rfl⟩
      map_add' v w := by
        ext g
        exact ((mk ρ U 1).comp (ρ g)).map_add v w
      map_smul' a v := by
        ext g
        exact ((mk ρ U 1).comp (ρ g)).map_smul a v }
  isIntertwining' g := by
    ext v x
    change mk ρ U 1 (ρ x (ρ g v)) = mk ρ U 1 (ρ (x * g) v)
    rw [map_mul]
    rfl

/-- For smooth input, each orbit function is a smooth induced vector. -/
def augmentation (P U : Subgroup G) (hPU : P ≤ Subgroup.normalizer U)
    (ρ : Representation R G V) (hρ : IsSmooth ρ) :
    ρ.IntertwiningMap (term P U hPU ρ) :=
  smoothLift hρ (fullAugmentation P U hPU ρ)

@[simp]
theorem augmentation_eval (P U : Subgroup G) (hPU : P ≤ Subgroup.normalizer U)
    (ρ : Representation R G V) (hρ : IsSmooth ρ) (v : V) (g : G) :
    Induction.eval P (inducing P U hPU ρ) (augmentation P U hPU ρ hρ v) g =
      mk ρ U 1 (ρ g v) := rfl

/-- Every transition carries the initial orbit-function map to the next one. -/
theorem map_augmentation (P U Q N : Subgroup G) (hPU : P ≤ Subgroup.normalizer U)
    (hQN : Q ≤ Subgroup.normalizer N) (hQP : Q ≤ P) (hUN : U ≤ N)
    (ρ : Representation R G V) (hρ : IsSmooth ρ) :
    (map P U Q N hPU hQN hQP hUN ρ).comp (augmentation P U hPU ρ hρ) =
      augmentation Q N hQN ρ hρ := by
  ext v g
  rfl

/-- Naturality of the initial map in every ambient intertwiner. -/
theorem augmentation_natural (P U : Subgroup G) (hPU : P ≤ Subgroup.normalizer U)
    {ρ : Representation R G V} {σ : Representation R G W}
    (hρ : IsSmooth ρ) (hσ : IsSmooth σ) (f : ρ.IntertwiningMap σ) :
    (termMap P U hPU f).comp (augmentation P U hPU ρ hρ) =
      (augmentation P U hPU σ hσ).comp f := by
  ext v g
  change mk σ U 1 (f (ρ g v)) = mk σ U 1 (σ g (f v))
  exact congrArg (mk σ U 1)
    (Representation.IntertwiningMap.isIntertwining ρ σ f g v)

end Langlands.Aubert.SubgroupTransition
