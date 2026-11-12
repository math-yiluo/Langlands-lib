import Langlands.Global.AdelicGLSiegelShape

/-! # Siegel finiteness for the actual adelic `GL(n)` Siegel sets -/

universe u

namespace Langlands.Global.PrimitiveAdelicHeight

/-- **Siegel finiteness for `GL(n)`.** For a Siegel set `Ω_N · diag(C) · A(c) · K` built from
a compact set `Ω_N` of unitriangular adelic matrices, a compact set `C` of norm-one ideles
and a constant `c > 0`, only finitely many rational invertible matrices `γ` move some point
of the Siegel set back into the Siegel set. -/
def SiegelSetGLFinitenessStatement : Prop :=
  ∀ (F : Type u) [Field F] [NumberField F] (n : ℕ)
    (ΩN : Set (Matrix (Fin n) (Fin n) (Adeles F))) (C : Set (Ideles F)) (c : ℝ),
    IsCompact ΩN → (∀ N ∈ ΩN, IsUnitriangular N) → IsCompact C →
      C ⊆ NormOneIdeleClass.normOneIdeles F → 0 < c →
      {γ : RationalGL F n | ∃ g ∈ siegelSetGL F n ΩN C c,
        AdelicGL.rational F n γ * g ∈ siegelSetGL F n ΩN C c}.Finite

end Langlands.Global.PrimitiveAdelicHeight
