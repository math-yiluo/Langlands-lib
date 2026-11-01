import Langlands.AlgebraicGeometry.FiniteEtale.Pullback

/-! # Automorphisms of finite-etale sections at an identity point -/

noncomputable section

open CategoryTheory AlgebraicGeometry

universe u

namespace Langlands.AlgebraicGeometry.FiniteEtale

variable {Ω : Type u} [Field Ω]
  (hs : ∀ Y : Cover (Spec (.of Ω)), Finite (Fiber (𝟙 (Spec (.of Ω))) Y))

/-- At the identity of a field spectrum, naturality on sections fixes every
point of every finite-etale object. Algebraic closure is unnecessary here. -/
theorem fundamentalGroup_identity_eq_one
    (g : FundamentalGroup (𝟙 (Spec (.of Ω))) hs) : g = 1 := by
  apply fundamentalGroup_ext
  intro Y x
  let T : Cover (Spec (.of Ω)) := cover (𝟙 _)
  let e : Fiber (𝟙 (Spec (.of Ω))) T := 𝟙 _
  let f : T ⟶ Y := ObjectProperty.homMk x
  have he : g • e = e := by
    apply Over.OverMorphism.ext
    simpa [T, cover, e] using (Over.w (g • e))
  calc
    g • x = g • (e ≫ f.hom) := rfl
    _ = (g • e) ≫ f.hom := smul_naturality _ hs f g e
    _ = x := by rw [he]; rfl
    _ = (1 : FundamentalGroup (𝟙 (Spec (.of Ω))) hs) • x := (one_smul _ x).symm

/-- The defined automorphism group at the identity point is trivial. -/
instance fundamentalGroup_identity_subsingleton :
    Subsingleton (FundamentalGroup (𝟙 (Spec (.of Ω))) hs) :=
  ⟨fun g h => (fundamentalGroup_identity_eq_one hs g).trans
    (fundamentalGroup_identity_eq_one hs h).symm⟩

end Langlands.AlgebraicGeometry.FiniteEtale
