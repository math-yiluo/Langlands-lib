import Langlands.GroupTheory.CocycleExtension
import Mathlib.Topology.Algebra.ContinuousMonoidHom

/-! # Cochain maps between normalized cocycle extensions -/

namespace Langlands.NormalizedTwoCocycle

universe u v w x y z

variable {G : Type u} {A : Type v} {H : Type w} {B : Type x}
  [Group G] [CommGroup A] [MulDistribMulAction G A]
  [Group H] [CommGroup B] [MulDistribMulAction H B]

/-- Cochain data for an extension map over the specified coefficient and group maps. -/
structure MapData (c : NormalizedTwoCocycle G A) (d : NormalizedTwoCocycle H B)
    (f : A →* B) (φ : G →* H) where
  cochain : G → B
  equivariant : ∀ g a, f (g • a) = φ g • f a
  compatible : ∀ g h, f (c (g, h)) * cochain (g * h) =
    cochain g * (φ g • cochain h) * d (φ g, φ h)

namespace MapData

variable {c : NormalizedTwoCocycle G A} {d : NormalizedTwoCocycle H B}
  {f : A →* B} {φ : G →* H} (m : MapData c d f φ)

@[simp] theorem cochain_one : m.cochain 1 = 1 := by
  have h := m.compatible 1 1
  simp only [map_one, one_left, one_mul, one_smul, mul_one] at h
  exact (mul_left_cancel (show m.cochain 1 * 1 = m.cochain 1 * m.cochain 1 by
    simpa using h)).symm

/-- The actual extension homomorphism `(a,g) ↦ (f(a) b(g), φ(g))`. -/
def toMonoidHom : c.Extension →* d.Extension where
  toFun t := ⟨f t.left * m.cochain t.right, φ t.right⟩
  map_one' := Extension.ext (by simp) (by simp)
  map_mul' s t := by
    apply Extension.ext
    · simp only [Extension.mul_left, Extension.mul_right, map_mul, m.equivariant,
        smul_mul']
      calc
        _ = (f s.left * (φ s.right • f t.left)) *
            (f (c (s.right, t.right)) * m.cochain (s.right * t.right)) := by ac_rfl
        _ = _ := by rw [m.compatible]; ac_rfl
    · exact map_mul φ s.right t.right

@[simp] theorem toMonoidHom_left (t : c.Extension) :
    (m.toMonoidHom t).left = f t.left * m.cochain t.right := rfl

@[simp] theorem toMonoidHom_right (t : c.Extension) :
    (m.toMonoidHom t).right = φ t.right := rfl

@[simp] theorem toMonoidHom_inl (a : A) :
    m.toMonoidHom (Extension.inl c a) = Extension.inl d (f a) := by
  apply Extension.ext <;> simp

@[simp] theorem projection_toMonoidHom (t : c.Extension) :
    Extension.projection d (m.toMonoidHom t) = φ (Extension.projection c t) := rfl

theorem toMonoidHom_sectionMap (g : G) :
    m.toMonoidHom (Extension.sectionMap c g) =
      Extension.inl d (m.cochain g) * Extension.sectionMap d (φ g) := by
  apply Extension.ext <;> simp

/-- The identity coefficient and group maps with constant-one cochain. -/
def id (c : NormalizedTwoCocycle G A) :
    MapData c c (MonoidHom.id A) (MonoidHom.id G) where
  cochain _ := 1
  equivariant _ _ := rfl
  compatible _ _ := by simp

@[simp] theorem toMonoidHom_id (c : NormalizedTwoCocycle G A) :
    (id c).toMonoidHom = MonoidHom.id c.Extension := by
  apply MonoidHom.ext
  intro t
  apply Extension.ext <;> simp [id]

variable {J : Type y} {C : Type z}
  [Group J] [CommGroup C] [MulDistribMulAction J C]
  {e : NormalizedTwoCocycle J C} {f' : B →* C} {φ' : H →* J}

/-- Composition uses the transported first cochain times the second cochain. -/
def comp (n : MapData d e f' φ') (m : MapData c d f φ) :
    MapData c e (f'.comp f) (φ'.comp φ) where
  cochain g := f' (m.cochain g) * n.cochain (φ g)
  equivariant g a := by
    simp only [MonoidHom.comp_apply, m.equivariant, n.equivariant]
  compatible g h := by
    simp only [MonoidHom.comp_apply, map_mul, smul_mul']
    calc
      _ = f' (f (c (g, h)) * m.cochain (g * h)) * n.cochain (φ g * φ h) := by
        rw [map_mul]
        ac_rfl
      _ = (f' (m.cochain g) * (φ' (φ g) • f' (m.cochain h))) *
          (f' (d (φ g, φ h)) * n.cochain (φ g * φ h)) := by
        rw [m.compatible, map_mul, map_mul, n.equivariant]
        ac_rfl
      _ = _ := by rw [n.compatible]; ac_rfl

@[simp] theorem toMonoidHom_comp (n : MapData d e f' φ') (m : MapData c d f φ) :
    (n.comp m).toMonoidHom = n.toMonoidHom.comp m.toMonoidHom := by
  apply MonoidHom.ext
  intro t
  apply Extension.ext
  · simp [comp, mul_assoc]
  · rfl

theorem injective (hf : Function.Injective f) (hφ : Function.Injective φ) :
    Function.Injective m.toMonoidHom := by
  intro s t h
  have hr : s.right = t.right := hφ (congrArg Extension.right h)
  apply Extension.ext _ hr
  apply hf
  have hl := congrArg Extension.left h
  simpa only [toMonoidHom_left, hr, mul_left_inj] using hl

theorem surjective (hf : Function.Surjective f) (hφ : Function.Surjective φ) :
    Function.Surjective m.toMonoidHom := by
  intro t
  obtain ⟨g, hg⟩ := hφ t.right
  obtain ⟨a, ha⟩ := hf (t.left / m.cochain g)
  exact ⟨⟨a, g⟩, Extension.ext (by simp [ha]) hg⟩

/-- Bijective maps of coefficients and acting groups give an actual extension equivalence. -/
noncomputable def toMulEquiv (hf : Function.Bijective f) (hφ : Function.Bijective φ) :
    c.Extension ≃* d.Extension :=
  MulEquiv.ofBijective m.toMonoidHom ⟨m.injective hf.1 hφ.1, m.surjective hf.2 hφ.2⟩

@[simp] theorem toMulEquiv_apply (hf : Function.Bijective f) (hφ : Function.Bijective φ)
    (t : c.Extension) : m.toMulEquiv hf hφ t = m.toMonoidHom t := rfl

/-- Equivalence with the inverse displayed in coefficient and group coordinates. -/
def equivOfEquivs (f : A ≃* B) (φ : G ≃* H)
    (m : MapData c d f.toMonoidHom φ.toMonoidHom) : c.Extension ≃* d.Extension where
  toFun := m.toMonoidHom
  invFun t := ⟨f.symm (t.left / m.cochain (φ.symm t.right)), φ.symm t.right⟩
  left_inv t := Extension.ext (by simp [toMonoidHom]) (by simp [toMonoidHom])
  right_inv t := Extension.ext (by simp [toMonoidHom]) (by simp [toMonoidHom])
  map_mul' := m.toMonoidHom.map_mul

section Topology

variable [TopologicalSpace G] [TopologicalSpace A]
  [TopologicalSpace H] [TopologicalSpace B] [ContinuousMul B]

theorem continuous (hf : Continuous f) (hφ : Continuous φ) (hb : Continuous m.cochain) :
    Continuous m.toMonoidHom := by
  apply continuous_induced_rng.mpr
  exact ((hf.comp (Extension.continuous_left c)).mul
    (hb.comp (Extension.continuous_right c))).prodMk
      (hφ.comp (Extension.continuous_right c))

end Topology

section TopologicalEquivalence

variable [TopologicalSpace G] [TopologicalSpace A]
  [TopologicalSpace H] [TopologicalSpace B] [IsTopologicalGroup B]

/-- Continuous component equivalences and cochain give a topological group equivalence. -/
def continuousEquivOfEquivs (f : A ≃ₜ* B) (φ : G ≃ₜ* H)
    (m : MapData c d f.toMulEquiv.toMonoidHom φ.toMulEquiv.toMonoidHom)
    (hb : Continuous m.cochain) : c.Extension ≃ₜ* d.Extension where
  toMulEquiv := equivOfEquivs f.toMulEquiv φ.toMulEquiv m
  continuous_toFun := m.continuous f.continuous φ.continuous hb
  continuous_invFun := by
    apply continuous_induced_rng.mpr
    exact (f.symm.continuous.comp ((Extension.continuous_left d).div'
      (hb.comp (φ.symm.continuous.comp (Extension.continuous_right d))))).prodMk
      (φ.symm.continuous.comp (Extension.continuous_right d))

end TopologicalEquivalence

end MapData

end Langlands.NormalizedTwoCocycle
