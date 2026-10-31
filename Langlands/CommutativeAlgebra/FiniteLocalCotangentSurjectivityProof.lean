import Langlands.CommutativeAlgebra.FiniteLocalCotangentSurjectivityStatement

/-!
# Cotangent surjectivity for finite maps of augmented local algebras

Let `mA` and `mB` be the kernels of the augmentations `r.comp f` and `r`. Cotangent
surjectivity says `mB ≤ f(mA)B + mB²`, so Nakayama's lemma for the finitely generated
`B`-module `mB` gives `mB ≤ f(mA)B`. Every element of `B` is a scalar plus an element of
`mB`, hence `B = f(A) + mA • B`. Nakayama's lemma for the finite `A`-module `B` then shows
that `f` is surjective.
-/

universe u v w

namespace Langlands.CommutativeAlgebra

/-- A finite map of local algebras with a common rational residue field is surjective if its
cotangent map is surjective and its target is Noetherian. -/
theorem finiteLocalCotangentSurjectivity :
    FiniteLocalCotangentSurjectivityStatement.{u, v, w} := by
  intro K _ A _ _ _ B _ _ _ _ r f
  let _ := f.toRingHom.toAlgebra
  intro hfin hcot
  have hrs : Function.Surjective r := fun c => ⟨algebraMap K B c, r.commutes c⟩
  have hrfs : Function.Surjective (r.comp f) :=
    fun c => ⟨algebraMap K A c, (r.comp f).commutes c⟩
  have hmB : RingHom.ker r.toRingHom ≤ Ideal.jacobson ⊥ := by
    rw [IsLocalRing.ker_eq_maximalIdeal r.toRingHom hrs]
    exact IsLocalRing.maximalIdeal_le_jacobson _
  have hmA : RingHom.ker (r.comp f).toRingHom ≤ Ideal.jacobson ⊥ := by
    rw [IsLocalRing.ker_eq_maximalIdeal (r.comp f).toRingHom hrfs]
    exact IsLocalRing.maximalIdeal_le_jacobson _
  -- Cotangent surjectivity: `mB ≤ f(mA)B + mB • mB`.
  have h1 : RingHom.ker r.toRingHom ≤
      Ideal.map f (RingHom.ker (r.comp f).toRingHom) ⊔
        RingHom.ker r.toRingHom • RingHom.ker r.toRingHom := by
    intro b hb
    obtain ⟨c, hc⟩ := hcot ((RingHom.ker r.toRingHom).toCotangent ⟨b, hb⟩)
    obtain ⟨a, rfl⟩ := (RingHom.ker (r.comp f).toRingHom).toCotangent_surjective c
    have hab : (RingHom.ker r.toRingHom).toCotangent ⟨f a, a.2⟩ =
        (RingHom.ker r.toRingHom).toCotangent ⟨b, hb⟩ := hc
    rw [Ideal.toCotangent_eq] at hab
    have hb' : b = f a - (f a - b) := by ring
    rw [hb']
    refine Submodule.sub_mem _ (Ideal.mem_sup_left (Ideal.mem_map_of_mem f a.2))
      (Ideal.mem_sup_right ?_)
    rw [Ideal.smul_eq_mul, ← pow_two]
    exact hab
  -- Nakayama over `B`: `mB ≤ f(mA)B`.
  have h2 : RingHom.ker r.toRingHom ≤ Ideal.map f (RingHom.ker (r.comp f).toRingHom) :=
    Submodule.le_of_le_smul_of_le_jacobson_bot (IsNoetherian.noetherian _) hmB h1
  -- `B = f(A) + mA • B`.
  have h3 : (⊤ : Submodule A B) ≤
      LinearMap.range (Algebra.linearMap A B) ⊔
        RingHom.ker (r.comp f).toRingHom • (⊤ : Submodule A B) := by
    intro b _
    have hb : b - algebraMap K B (r b) ∈ RingHom.ker r.toRingHom := by
      rw [RingHom.mem_ker]
      change r (b - algebraMap K B (r b)) = 0
      rw [map_sub, r.commutes, Algebra.algebraMap_self, RingHom.id_apply, sub_self]
    have hsplit : b = Algebra.linearMap A B (algebraMap K A (r b)) +
        (b - algebraMap K B (r b)) := by
      change b = f (algebraMap K A (r b)) + (b - algebraMap K B (r b))
      rw [f.commutes]
      ring
    rw [hsplit]
    refine Submodule.add_mem_sup ⟨_, rfl⟩ ?_
    rw [Ideal.smul_top_eq_map]
    exact h2 hb
  -- Nakayama over `A`: the image of `f` is all of `B`.
  have h4 := Submodule.le_of_le_smul_of_le_jacobson_bot (Module.finite_def.mp hfin) hmA h3
  intro b
  obtain ⟨a, ha⟩ := h4 (Submodule.mem_top (x := b))
  exact ⟨a, ha⟩

end Langlands.CommutativeAlgebra
