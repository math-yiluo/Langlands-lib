import Langlands.Representation.Exponents.LeviNormalizerBridge

/-! # Finite representatives for normalizers of split-component centralizers -/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry
open scoped CategoryTheory.MonObj

namespace Langlands.GroupScheme

variable {k : Type u} [Field k]
  {G M : GroupScheme (Spec (CommRingCat.of k))}

/-- Rational points whose conjugation restricts to an automorphism of a
specified group-scheme representative. -/
def representativeNormalizerPoints (j : M ⟶ G) : Subgroup (rationalPoints G) where
  carrier := {w | ∃ φ : M ≅ M, φ.hom ≫ j = j ≫ (G.innerIso w).hom}
  one_mem' := ⟨Iso.refl M, by
    rw [Iso.refl_hom, innerIso_one_hom, Category.id_comp, Category.comp_id]⟩
  mul_mem' := by
    rintro w v ⟨φ, hφ⟩ ⟨ψ, hψ⟩
    refine ⟨ψ ≪≫ φ, ?_⟩
    rw [Iso.trans_hom, Category.assoc, hφ, ← Category.assoc, hψ,
      Category.assoc, innerIso_mul_hom]
  inv_mem' := by
    rintro w ⟨φ, hφ⟩
    refine ⟨φ.symm, ?_⟩
    change φ.inv ≫ j = j ≫ (G.innerIso w⁻¹).hom
    rw [innerIso_inv_hom]
    apply (cancel_mono (G.innerIso w).hom).mp
    rw [Category.assoc, ← hφ, ← Category.assoc, Iso.inv_hom_id,
      Category.id_comp, Category.assoc, Iso.inv_hom_id, Category.comp_id]

section Finite

variable [IsAffineHom G.X.hom] [LocallyOfFiniteType G.X.hom]
  [IsAffineHom M.X.hom]
  {A : CommGroupScheme (Spec (CommRingCat.of k))} {a : A.toGrp ⟶ M}
  {j : M ⟶ G}

/-- A closed representative that is the centralizer of its split component has
finitely many rational normalizer cosets, with representatives in that normalizer. -/
theorem IsSplitComponent.exists_finite_normalizer_representatives
    (ha : IsSplitComponent a) (hj : IsClosedSubgroup j)
    (hZ : torusCentralizer (a ≫ j) = SubgroupFunctor.range j) :
    ∃ (n : ℕ) (g : Fin n → rationalPoints G),
      (∀ t, ∃ φ : M ≅ M, φ.hom ≫ j = j ≫ (G.innerIso (g t)).hom) ∧
      ∀ (w : rationalPoints G) (φ : M ≅ M),
        φ.hom ≫ j = j ≫ (G.innerIso w).hom →
          ∃ (t : Fin n) (m : rationalPoints M), w = g t * rationalPoints.map j m := by
  classical
  have hi : IsClosedSubgroup (a ≫ j) := ha.1.1.2.comp hj
  have : IsClosedImmersion (a ≫ j).hom.hom.left := hi
  have : Finite (weylImage (a ≫ j)) :=
    splitTorusWeylImageFinite k G A ha.1.1.1 (a ≫ j) hi
  let N := representativeNormalizerPoints j
  let liftN : N → normalizerPoints (a ≫ j) := fun w =>
    ⟨w.1, ⟨ha.automorphismRestrictionIso w.2.choose,
      ha.isNormalizingPoint_of_normalizes w.2.choose_spec⟩⟩
  let f : N → weylImage (a ≫ j) := fun w =>
    ⟨weylAction (a ≫ j) (liftN w), ⟨liftN w, rfl⟩⟩
  let Q := Set.range f
  let r : Q → N := fun q => q.2.choose
  have hr (q : Q) : f (r q) = q.1 := q.2.choose_spec
  let : Fintype Q := Fintype.ofFinite Q
  let e : Q ≃ Fin (Fintype.card Q) := Fintype.equivFin Q
  refine ⟨Fintype.card Q, fun t => (r (e.symm t)).1, ?_, ?_⟩
  · intro t
    exact (r (e.symm t)).2
  · intro w φ hw
    let nw : N := ⟨w, ⟨φ, hw⟩⟩
    let q : Q := ⟨f nw, ⟨nw, rfl⟩⟩
    have hweyl : weylAction (a ≫ j) (liftN (r q)) =
        weylAction (a ≫ j) (liftN nw) :=
      congrArg Subtype.val (hr q)
    have hker : weylAction (a ≫ j) ((liftN (r q))⁻¹ * liftN nw) = 1 := by
      rw [map_mul, map_inv, hweyl, inv_mul_cancel]
    have hcent := (ha.1.1.1.weylAction_eq_one_iff (a ≫ j) _).mp hker
    have htor : (r q).1⁻¹ * w ∈ (torusCentralizer (a ≫ j)).carrier
        (Over.mk (𝟙 (Spec (CommRingCat.of k)))) :=
      (mem_torusCentralizer_base_iff (a ≫ j) _).mpr
        ((mem_centralizerPoints (a ≫ j)).mp hcent)
    rw [hZ] at htor
    obtain ⟨m, hm⟩ := SubgroupFunctor.mem_range.mp htor
    have hm' : rationalPoints.map j m = (r q).1⁻¹ * w := hm
    refine ⟨e q, m, ?_⟩
    change w = (r (e.symm (e q))).1 * rationalPoints.map j m
    rw [e.symm_apply_apply]
    exact (eq_inv_mul_iff_mul_eq.mp hm').symm

end Finite

end Langlands.GroupScheme
