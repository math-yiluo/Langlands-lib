import Langlands.AllFieldBZ.Representation.Filtration.VanishingStatement
import Langlands.Representation.Filtration.SimpleSubquotientFactorProof

/-!
# All-field port of `Langlands.Representation.Filtration.SimpleSubquotientFactorProof`

Mechanical port of the field-dependent declarations of the p-adic module
`Langlands.Representation.Filtration.SimpleSubquotientFactorProof` to an arbitrary nonarchimedean local field
(`Langlands.AllFieldBZ.LocalFieldPackage`). See the paired Markdown.
-/
namespace Langlands.AllFieldBZ
universe uK uG uV uW

private theorem _root_.Langlands.intertwiner_descends
    {k G X Y Z : Type*} [Field k] [Monoid G]
    [AddCommGroup X] [Module k X] [AddCommGroup Y] [Module k Y]
    [AddCommGroup Z] [Module k Z]
    {ρ : Representation k G X} {σ : Representation k G Y} {τ : Representation k G Z}
    (g : ρ.IntertwiningMap σ) (f : ρ.IntertwiningMap τ)
    (hg : Function.Surjective g) (hker : g.toLinearMap.ker ≤ f.toLinearMap.ker) :
    ∃ h : σ.IntertwiningMap τ, ∀ x, h (g x) = f x := by
  let l : Y →ₗ[k] Z :=
    (g.toLinearMap.ker.liftQ f.toLinearMap hker).comp
      (g.toLinearMap.quotKerEquivOfSurjective hg).symm.toLinearMap
  have hl (x : X) : l (g x) = f x := by
    change (g.toLinearMap.ker.liftQ f.toLinearMap hker)
      ((g.toLinearMap.quotKerEquivOfSurjective hg).symm (g.toLinearMap x)) = f x
    rw [LinearMap.quotKerEquivOfSurjective_symm_apply]
    rfl
  refine ⟨⟨l, fun a => ?_⟩, hl⟩
  ext y
  obtain ⟨x, rfl⟩ := hg y
  change l (σ a (g x)) = τ a (l (g x))
  rw [← Representation.IntertwiningMap.isIntertwining _ _ g a x, hl, hl]
  exact Representation.IntertwiningMap.isIntertwining _ _ f a x

end Langlands.AllFieldBZ
