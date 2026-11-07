import Langlands.GroupTheory.CocycleSplittingModule

noncomputable section

universe u

open CategoryTheory CategoryTheory.Limits

namespace Langlands.NormalizedTwoCocycle.SplittingModule

set_option backward.isDefEq.respectTransparency false

attribute [-instance] ULift.module

variable {G A : Type u} [Group G] [Fintype G] [CommGroup A]
  [MulDistribMulAction G A] (c : NormalizedTwoCocycle G A)

local instance : Module Scalars.{u} (Additive A) := ULift.module

local instance : Module Scalars.{u} (Rep.ofMulDistribMulAction G A) := ULift.module

abbrev coefficientAction (g : G) : Additive A →ₗ[Scalars.{u}] Additive A :=
  (coefficientRepresentation G A).ρ g

omit [Fintype G] in
lemma additive_cocycle (g h j : G) :
    Additive.ofMul (c (g * h, j)) + Additive.ofMul (c (g, h)) =
      coefficientAction g (Additive.ofMul (c (h, j))) + Additive.ofMul (c (g, h * j)) :=
  congrArg Additive.ofMul (c.cocycle g h j)

/-- The correction term in the cocycle splitting-module action. -/
def twist (g : G) : (G → Scalars.{u}) →ₗ[Scalars.{u}] Additive A where
  toFun f := ∑ x : G, f x • Additive.ofMul (c (g, x⁻¹))
  map_add' f k := by simp [add_smul, Finset.sum_add_distrib]
  map_smul' r f := by simp [smul_smul, Finset.smul_sum]

lemma twist_apply (g : G) (f : G → Scalars.{u}) :
    twist c g f = ∑ x : G, f x • Additive.ofMul (c (g, x⁻¹)) := rfl

@[simp] lemma twist_one (f : G → Scalars.{u}) : twist c 1 f = 0 := by
  simp [twist_apply]

lemma twist_regular (g h : G) (f : G → Scalars.{u}) :
    twist c g ((regular G).ρ h f) =
      ∑ x : G, f x • Additive.ofMul (c (g, h * x⁻¹)) := by
  rw [twist_apply]
  calc
    _ = ∑ x : G, f (x * h) • Additive.ofMul (c (g, h * (x * h)⁻¹)) := by
      simp only [regular_apply, mul_inv_rev, mul_inv_cancel_left]
    _ = _ := Equiv.sum_comp (Equiv.mulRight h)
      (fun x => f x • Additive.ofMul (c (g, h * x⁻¹)))

lemma twist_cocycle (g h : G) (f : G → Scalars.{u}) :
    twist c (g * h) f + coordinateSum G f • Additive.ofMul (c (g, h)) =
      coefficientAction g (twist c h f) + twist c g ((regular G).ρ h f) := by
  rw [twist_regular]
  simp only [twist_apply, coordinateSum_apply, Finset.sum_smul, map_sum, map_smul,
    ← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro x _
  rw [← smul_add, ← smul_add, additive_cocycle]

lemma twist_mul (g h : G) (f : Ideal G) :
    twist c (g * h) f.val =
      coefficientAction g (twist c h f.val) + twist c g ((ideal G).ρ h f).val := by
  have hf : coordinateSum G f.val = 0 := f.property
  change twist c (g * h) f.val =
    coefficientAction g (twist c h f.val) + twist c g ((regular G).ρ h f.val)
  simpa only [hf, zero_smul, add_zero] using twist_cocycle c g h f.val

/-- Underlying carrier of the cocycle splitting module. -/
abbrev Carrier := Additive A × Ideal G

/-- The actual action on the cocycle splitting module. -/
def action (g : G) : Carrier (G := G) (A := A) →ₗ[Scalars.{u}]
    Carrier (G := G) (A := A) where
  toFun x := (coefficientAction g x.1 + twist c g x.2.val, (ideal G).ρ g x.2)
  map_add' x y := by
    apply Prod.ext
    · change coefficientAction g (x.1 + y.1) + twist c g (x.2.val + y.2.val) =
        (coefficientAction g x.1 + twist c g x.2.val) +
          (coefficientAction g y.1 + twist c g y.2.val)
      rw [map_add, map_add]
      abel
    · exact map_add ((ideal G).ρ g) x.2 y.2
  map_smul' r x := by
    apply Prod.ext
    · change coefficientAction g (r • x.1) + twist c g (r • x.2.val) =
        r • (coefficientAction g x.1 + twist c g x.2.val)
      rw [map_smul, map_smul, smul_add]
    · exact map_smul ((ideal G).ρ g) r x.2

/-- The splitting representation attached to the actual normalized cocycle. -/
def splitting : Rep.{u} Scalars.{u} G :=
  Rep.of (X := Carrier (G := G) (A := A))
    { toFun := action c
      map_one' := by
        apply LinearMap.ext
        intro x
        apply Prod.ext
        · change coefficientAction 1 x.1 + twist c 1 x.2.val = x.1
          simp [coefficientAction]
        · exact LinearMap.congr_fun (map_one (ideal G).ρ) x.2
      map_mul' g h := by
        apply LinearMap.ext
        intro x
        apply Prod.ext
        · change coefficientAction (g * h) x.1 + twist c (g * h) x.2.val =
            coefficientAction g (coefficientAction h x.1 + twist c h x.2.val) +
              twist c g ((ideal G).ρ h x.2).val
          rw [coefficientAction, map_mul, Module.End.mul_apply, map_add, twist_mul]
          abel
        · exact LinearMap.congr_fun (map_mul (ideal G).ρ g h) x.2 }

/-- Inclusion of the coefficient module into the splitting module. -/
def inclusion : coefficientRepresentation G A ⟶ splitting c :=
  Rep.ofHom ⟨LinearMap.inl Scalars.{u} (Additive A) (Ideal G), fun g => by
    apply LinearMap.ext
    intro a
    change Additive A at a
    change (coefficientAction g a, 0) =
      (coefficientAction g a + twist c g 0, (ideal G).ρ g 0)
    simp⟩

/-- Projection of the splitting module onto the augmentation ideal. -/
def projection : splitting c ⟶ ideal G :=
  Rep.ofHom ⟨LinearMap.snd Scalars.{u} (Additive A) (Ideal G), fun _ => rfl⟩

/-- The exact sequence whose second connecting map represents the cocycle. -/
def sequence : ShortComplex (Rep.{u} Scalars.{u} G) :=
  ShortComplex.mk (inclusion c) (projection c) (by
    apply Rep.hom_ext
    apply Representation.IntertwiningMap.ext
    apply LinearMap.ext
    intro a
    rfl)

lemma sequence_shortExact : (sequence c).ShortExact where
  exact := (forget₂ (Rep.{u} Scalars.{u} G) (ModuleCat Scalars.{u})).reflects_exact_of_faithful _ <|
    (ShortComplex.moduleCat_exact_iff _).2 fun x hx => by
      change x.2 = 0 at hx
      exact ⟨x.1, Prod.ext rfl hx.symm⟩
  mono_f := (Rep.mono_iff_injective _).2 fun _ _ h => congrArg Prod.fst h
  epi_g := (Rep.epi_iff_surjective _).2 fun f => ⟨(0, f), rfl⟩

/-- The displayed product coordinates split the sequence after forgetting the action. -/
def sequence_scalarSplitting :
    ((sequence c).map (forget₂ (Rep.{u} Scalars.{u} G)
      (ModuleCat Scalars.{u}))).Splitting where
  r := ModuleCat.ofHom (LinearMap.fst Scalars.{u} (Additive A) (Ideal G))
  s := ModuleCat.ofHom (LinearMap.inr Scalars.{u} (Additive A) (Ideal G))
  f_r := by ext a; rfl
  s_g := by ext f; rfl
  id := by
    apply ModuleCat.hom_ext
    apply LinearMap.ext
    intro x
    change (x.1, (0 : Ideal G)) + (0, x.2) = x
    exact Prod.ext (add_zero _) (zero_add _)

/-- A scalar section of augmentation, supported at the identity coordinate. -/
def augmentationSection : Scalars.{u} →ₗ[Scalars.{u}] (G → Scalars.{u}) :=
  (LinearMap.id : Scalars.{u} →ₗ[Scalars.{u}] Scalars.{u}).smulRight (delta G 1)

lemma augmentationSection_sum (r : Scalars.{u}) :
    coordinateSum G (augmentationSection (G := G) r) = r := by
  change coordinateSum G (r • delta G 1) = r
  rw [map_smul, coordinateSum_delta, smul_eq_mul, mul_one]

/-- The augmentation sequence splits over the scalar ring. -/
def idealSequence_scalarSplitting :
    ((idealSequence G).map (forget₂ (Rep.{u} Scalars.{u} G)
      (ModuleCat Scalars.{u}))).Splitting := by
  let hS := (idealSequence_shortExact G).map_of_exact
    (forget₂ (Rep.{u} Scalars.{u} G) (ModuleCat Scalars.{u}))
  exact ShortComplex.Splitting.ofExactOfSection _ hS.exact
    (ModuleCat.ofHom (augmentationSection (G := G)))
    (by
      apply ModuleCat.hom_ext
      apply LinearMap.ext
      intro r
      exact augmentationSection_sum r)
    hS.mono_f

end Langlands.NormalizedTwoCocycle.SplittingModule
