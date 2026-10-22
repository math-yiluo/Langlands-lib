import Langlands.Representation.Smooth.SmoothPart.HomStatement

/-! # Smooth-part linear factorization laws -/

namespace Langlands

universe uR uG uV uW uU

variable {R : Type uR} {G : Type uG} {V : Type uV} {W : Type uW} {U : Type uU}
variable [CommRing R] [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
variable [AddCommGroup V] [Module R V] [AddCommGroup W] [Module R W]
variable [AddCommGroup U] [Module R U]
variable {ρ : Representation R G V} {σ : Representation R G W}
variable {τ : Representation R G U}

theorem smoothHomEquiv_apply (hρ : IsSmooth ρ) (f : ρ.IntertwiningMap σ) (v : V) :
    (smoothHomEquiv hρ σ f v : W) = f v := rfl

theorem smoothHomEquiv_symm_apply (hρ : IsSmooth ρ)
    (f : ρ.IntertwiningMap (smoothPart σ)) (v : V) :
    (smoothHomEquiv hρ σ).symm f v = (f v : W) := rfl

theorem smoothHomEquiv_postcomp (hρ : IsSmooth ρ)
    (f : ρ.IntertwiningMap σ) (g : σ.IntertwiningMap τ) :
    smoothHomEquiv hρ τ (g.comp f) =
      (smoothMap g).comp (smoothHomEquiv hρ σ f) := by
  ext v
  rfl

theorem smoothHomEquiv_precomp (hρ : IsSmooth ρ) (hτ : IsSmooth τ)
    (f : ρ.IntertwiningMap σ) (g : τ.IntertwiningMap ρ) :
    smoothHomEquiv hτ σ (f.comp g) = (smoothHomEquiv hρ σ f).comp g := by
  ext v
  rfl

omit [IsTopologicalGroup G] in
theorem smoothHomLaws :
    SmoothHomLawsStatement (R := R) (G := G) (V := V) (W := W) (U := U) := by
  intro _
  exact ⟨fun _ _ hρ f v => smoothHomEquiv_apply hρ f v,
    fun _ _ hρ f v => smoothHomEquiv_symm_apply hρ f v,
    fun _ _ _ hρ f g => smoothHomEquiv_postcomp hρ f g,
    fun _ _ _ hρ hτ f g => smoothHomEquiv_precomp hρ hτ f g⟩

end Langlands
