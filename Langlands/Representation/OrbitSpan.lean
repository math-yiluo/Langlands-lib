import Mathlib.RepresentationTheory.Irreducible

/-! # Spanning by a nonzero orbit in an irreducible representation -/

namespace Langlands

universe uG uW

variable {k : Type*} [Field k] {G : Type uG} [Group G]
  {V : Type uW} [AddCommGroup V] [Module k V]

/-- In an irreducible representation, the orbit of a nonzero vector spans. -/
theorem span_range_orbit_eq_top {ρ : Representation k G V} (hρ : ρ.IsIrreducible)
    {v : V} (hv : v ≠ 0) :
    Submodule.span k (Set.range fun g : G => ρ g v) = ⊤ := by
  let S : Subrepresentation ρ :=
    { toSubmodule := Submodule.span k (Set.range fun g : G => ρ g v)
      apply_mem_toSubmodule := by
        intro g w hw
        have hle : Submodule.span k (Set.range fun h : G => ρ h v) ≤
            (Submodule.span k (Set.range fun h : G => ρ h v)).comap (ρ g) := by
          rw [Submodule.span_le]
          rintro _ ⟨h, rfl⟩
          rw [SetLike.mem_coe, Submodule.mem_comap]
          exact Submodule.subset_span ⟨g * h, by simp [map_mul, Module.End.mul_apply]⟩
        exact hle hw }
  have hvS : v ∈ S.toSubmodule := Submodule.subset_span ⟨1, by simp⟩
  rcases eq_bot_or_eq_top S with h | h
  · exfalso
    apply hv
    rw [h] at hvS
    change v ∈ (⊥ : Submodule k V) at hvS
    exact (Submodule.mem_bot k).mp hvS
  · exact congrArg Subrepresentation.toSubmodule h

end Langlands
