import Langlands.Representation.Smooth.SmoothPart.FunctorialityStatement

/-! # Smooth-part maps and the smooth equivalence -/

namespace Langlands

universe uR uG uV uW uU

variable {R : Type uR} {G : Type uG} {V : Type uV} {W : Type uW} {U : Type uU}
variable [CommRing R] [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
variable [AddCommGroup V] [Module R V] [AddCommGroup W] [Module R W]
variable [AddCommGroup U] [Module R U]
variable {ρ : Representation R G V} {σ : Representation R G W}

theorem smoothInclusion_comp_smoothMap (f : ρ.IntertwiningMap σ) :
    (smoothInclusion σ).comp (smoothMap f) = f.comp (smoothInclusion ρ) := by
  ext v
  rfl

theorem smoothMap_id :
    smoothMap (Representation.IntertwiningMap.id ρ) =
      Representation.IntertwiningMap.id (smoothPart ρ) := by
  ext v
  rfl

theorem smoothMap_comp {τ : Representation R G U}
    (f : ρ.IntertwiningMap σ) (g : σ.IntertwiningMap τ) :
    smoothMap (g.comp f) = (smoothMap g).comp (smoothMap f) := by
  ext v
  rfl

theorem smoothEquiv_apply (hρ : IsSmooth ρ) (v : smoothVectors ρ) :
    smoothEquiv hρ v = (v : V) :=
  rfl

omit [IsTopologicalGroup G] in
theorem smoothPartFunctoriality :
    SmoothPartFunctorialityStatement (R := R) (G := G) (V := V) (W := W) (U := U) := by
  intro _
  exact ⟨fun _ _ f => smoothInclusion_comp_smoothMap f, fun _ => smoothMap_id,
    fun _ _ _ f g => smoothMap_comp f g, fun _ hρ v => smoothEquiv_apply hρ v⟩

end Langlands
