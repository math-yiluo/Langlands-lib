import Langlands.Representation.Smooth.FixedVectors.LawsStatement

namespace Langlands

universe uR uG uV uW uU

variable {R : Type uR} {G : Type uG} {V : Type uV} {W : Type uW} {U : Type uU}
variable [CommRing R] [Group G]
variable [AddCommGroup V] [Module R V] [AddCommGroup W] [Module R W]
variable [AddCommGroup U] [Module R U]
variable {ρ : Representation R G V} {σ : Representation R G W}
variable {τ : Representation R G U}

theorem map_mem_fixedVectors (f : ρ.IntertwiningMap σ) {K : Subgroup G} {v : V}
    (hv : v ∈ fixedVectors ρ K) : f v ∈ fixedVectors σ K :=
  (fixedVectorsMap f K ⟨v, hv⟩).property

@[simp]
theorem fixedVectorsMap_apply (f : ρ.IntertwiningMap σ) (K : Subgroup G)
    (v : fixedVectors ρ K) : (fixedVectorsMap f K v : W) = f (v : V) :=
  rfl

theorem subtype_comp_fixedVectorsMap (f : ρ.IntertwiningMap σ) (K : Subgroup G) :
    (fixedVectors σ K).subtype.comp (fixedVectorsMap f K) =
      f.toLinearMap.comp (fixedVectors ρ K).subtype :=
  rfl

@[simp]
theorem fixedVectorsMap_id (ρ : Representation R G V) (K : Subgroup G) :
    fixedVectorsMap (Representation.IntertwiningMap.id ρ) K = LinearMap.id := by
  ext v
  rfl

@[simp]
theorem fixedVectorsMap_comp (g : σ.IntertwiningMap τ) (f : ρ.IntertwiningMap σ)
    (K : Subgroup G) :
    fixedVectorsMap (g.comp f) K = (fixedVectorsMap g K).comp (fixedVectorsMap f K) := by
  ext v
  rfl

theorem fixedVectorsMap_injective (f : ρ.IntertwiningMap σ)
    (hf : Function.Injective f) (K : Subgroup G) :
    Function.Injective (fixedVectorsMap f K) := by
  intro v w hvw
  apply Subtype.ext
  apply hf
  exact congrArg Subtype.val hvw

theorem fixedVectorsMapLaws :
    FixedVectorsMapLawsStatement (R := R) (G := G) (V := V) (W := W) (U := U) := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro ρ σ f K v hv
    exact map_mem_fixedVectors f hv
  · intro ρ σ f K v
    exact fixedVectorsMap_apply f K v
  · intro ρ σ f K
    exact subtype_comp_fixedVectorsMap f K
  · intro ρ K
    exact fixedVectorsMap_id ρ K
  · intro ρ σ τ g f K
    exact fixedVectorsMap_comp g f K
  · intro ρ σ f hf K
    exact fixedVectorsMap_injective f hf K

@[simp]
theorem fixedVectorsEquiv_apply (e : ρ.Equiv σ) (K : Subgroup G)
    (v : fixedVectors ρ K) : (fixedVectorsEquiv e K v : W) = e (v : V) :=
  rfl

@[simp]
theorem fixedVectorsEquiv_symm_apply (e : ρ.Equiv σ) (K : Subgroup G)
    (w : fixedVectors σ K) : ((fixedVectorsEquiv e K).symm w : V) = e.symm (w : W) :=
  rfl

@[simp]
theorem fixedVectorsEquiv_toLinearMap (e : ρ.Equiv σ) (K : Subgroup G) :
    (fixedVectorsEquiv e K).toLinearMap = fixedVectorsMap e.toIntertwiningMap K :=
  rfl

@[simp]
theorem fixedVectorsEquiv_symm (e : ρ.Equiv σ) (K : Subgroup G) :
    (fixedVectorsEquiv e K).symm = fixedVectorsEquiv e.symm K := by
  ext v
  rfl

theorem fixedVectorsEquivalenceLaws :
    FixedVectorsEquivalenceLawsStatement (R := R) (G := G) (V := V) (W := W) := by
  intro ρ σ e K
  exact ⟨fixedVectorsEquiv_apply e K, fixedVectorsEquiv_symm_apply e K,
    fixedVectorsEquiv_toLinearMap e K, fixedVectorsEquiv_symm e K⟩


/-- All map and equivalence restriction laws, with their full quantifiers. -/
theorem fixedVectorsLaws :
    FixedVectorsLawsStatement (R := R) (G := G) (V := V) (W := W) (U := U) :=
  ⟨fixedVectorsMapLaws, fixedVectorsEquivalenceLaws⟩

end Langlands
