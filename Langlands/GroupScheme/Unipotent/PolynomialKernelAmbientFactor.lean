import Langlands.GroupScheme.Unipotent.PolynomialKernelBaseChange

/-! # Ambient vector factors for additive polynomial kernels -/

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true
set_option maxHeartbeats 800000

noncomputable section

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Polynomial
open CategoryTheory.MonoidalCategory CategoryTheory.CartesianMonoidalCategory
open scoped CategoryTheory.MonObj BigOperators

namespace Langlands.GroupScheme.Unipotent

open OneDimensional RelativeRoot

variable {k : Type u} [Field k]

section CompatibleMaps

variable {n r m : ℕ}
    (f : Fin n → k[X]) (hf : ∀ i, IsAdditive (f i))
    (g : Fin m → k[X]) (hg : ∀ i, IsAdditive (g i))
    (e : VectorGroup.groupScheme (CommRingCat.of k) n ≅
      VectorGroup.groupScheme (CommRingCat.of k) r ⊗
        VectorGroup.groupScheme (CommRingCat.of k) m)

/-- The first ambient factor, as an actual section into the original vector
group. -/
def polynomialKernelAmbientSection :
    VectorGroup.groupScheme (CommRingCat.of k) r ⟶
      VectorGroup.groupScheme (CommRingCat.of k) n :=
  lift (𝟙 _) 0 ≫ e.inv

/-- The actual projection to the first ambient factor. -/
def polynomialKernelAmbientRetraction :
    VectorGroup.groupScheme (CommRingCat.of k) n ⟶
      VectorGroup.groupScheme (CommRingCat.of k) r :=
  e.hom ≫ fst _ _

@[reassoc (attr := simp)]
theorem polynomialKernelAmbientSection_comp_retraction :
    polynomialKernelAmbientSection e ≫ polynomialKernelAmbientRetraction e = 𝟙 _ := by
  simp [polynomialKernelAmbientSection, polynomialKernelAmbientRetraction, Category.assoc]

/-- The ambient factor is an actual closed vector subgroup. -/
theorem polynomialKernelAmbientSection_isClosedSubgroup :
    IsClosedSubgroup (polynomialKernelAmbientSection e) := by
  have : IsAffineHom (VectorGroup.groupScheme (CommRingCat.of k) n).X.hom := by
    change IsAffineHom (Spec.map
      (CommRingCat.ofHom (algebraMap k (MvPolynomial (Fin n) k))))
    infer_instance
  exact LinearKernelTower.isClosedSubgroup_of_section
    (polynomialKernelAmbientRetraction e) (polynomialKernelAmbientSection e)
    (polynomialKernelAmbientSection_comp_retraction e)

variable (he : e.hom ≫ snd _ _ ≫ polynomialRow g hg = polynomialRow f hf)

/-- The ambient factor is annihilated by the original polynomial row. -/
@[reassoc (attr := simp)]
theorem polynomialKernelAmbientSection_comp_row
    (he : e.hom ≫ snd _ _ ≫ polynomialRow g hg = polynomialRow f hf) :
    polynomialKernelAmbientSection e ≫ polynomialRow f hf = 0 := by
  rw [← he]
  simp [polynomialKernelAmbientSection, Category.assoc]

/-- The compatible ambient decomposition restricts to the actual kernels. -/
def polynomialKernelAmbientKernelIso :
    kernel (polynomialRow f hf) ≅
      VectorGroup.groupScheme (CommRingCat.of k) r ⊗ kernel (polynomialRow g hg) :=
  kernelCoordinateIso (snd _ _ ≫ polynomialRow g hg) (polynomialRow f hf) e he ≪≫
    kernelSndIso _ _

@[reassoc (attr := simp)]
theorem polynomialKernelAmbientKernelIso_hom_fst :
    (polynomialKernelAmbientKernelIso f hf g hg e he).hom ≫ fst _ _ =
      kernelι (polynomialRow f hf) ≫ polynomialKernelAmbientRetraction e := by
  simp [polynomialKernelAmbientKernelIso, polynomialKernelAmbientRetraction, Category.assoc]

@[reassoc (attr := simp)]
theorem polynomialKernelAmbientKernelIso_hom_snd_ι :
    (polynomialKernelAmbientKernelIso f hf g hg e he).hom ≫ snd _ _ ≫
      kernelι (polynomialRow g hg) =
        kernelι (polynomialRow f hf) ≫ e.hom ≫ snd _ _ := by
  simp [polynomialKernelAmbientKernelIso, Category.assoc]

@[reassoc (attr := simp)]
theorem polynomialKernelAmbientKernelIso_inv_ι :
    (polynomialKernelAmbientKernelIso f hf g hg e he).inv ≫
      kernelι (polynomialRow f hf) =
        (𝟙 _ ⊗ₘ kernelι (polynomialRow g hg)) ≫ e.inv := by
  simp [polynomialKernelAmbientKernelIso, Category.assoc]

/-- Including the vector factor in the decomposed kernel agrees with the
ambient section. -/
@[reassoc (attr := simp)]
theorem polynomialKernelAmbientKernelIso_section_ι :
    lift (𝟙 _) 0 ≫ (polynomialKernelAmbientKernelIso f hf g hg e he).inv ≫
      kernelι (polynomialRow f hf) = polynomialKernelAmbientSection e := by
  simp [polynomialKernelAmbientSection]

end CompatibleMaps

/-- The actual row in zero variables is zero. -/
theorem polynomialRow_zeroVariables
    (f : Fin 0 → k[X]) (hf : ∀ i, IsAdditive (f i)) :
    polynomialRow f hf = 0 := by
  apply hom_ext_points
  intro T x
  rw [comp_polynomialRow, Grp.zero_hom, Mon.zero_hom, ← Hom.one_def, MonObj.comp_one]
  apply VectorGroup.points_ext
  intro j
  rw [polynomialRowPoints_coord]
  simp only [Finset.univ_eq_empty, Finset.sum_empty]
  exact (congrArg (fun y => y.toAdd j)
    (VectorGroup.coordinates (CommRingCat.of k) 1 T).map_one).symm

/-- A zero actual polynomial row has zero polynomial coefficients, as detected
on the affine-line test with one universal nonzero coordinate at a time. -/
theorem polynomialRow_eq_zero_iff {n : ℕ}
    (f : Fin n → k[X]) (hf : ∀ i, IsAdditive (f i)) :
    polynomialRow f hf = 0 ↔ f = 0 := by
  classical
  constructor
  · intro h
    funext j
    let A := AffineLine.scheme (Spec (CommRingCat.of k))
    let x : A ⟶ (VectorGroup.groupScheme (CommRingCat.of k) n).X :=
      (VectorGroup.coordinates (CommRingCat.of k) n A).symm
        (Multiplicative.ofAdd fun i =>
          if i = j then AffineLine.coord (Spec (CommRingCat.of k)) else 0)
    have hx : x ≫ (polynomialRow f hf).hom.hom = 1 := by
      rw [h, Grp.zero_hom, Mon.zero_hom, ← Hom.one_def, MonObj.comp_one]
    have hsum := (comp_polynomialRow_eq_one_iff f hf A x).mp hx
    have hcoord : ∀ i, (VectorGroup.coordinates (CommRingCat.of k) n A x).toAdd i =
        if i = j then AffineLine.coord (Spec (CommRingCat.of k)) else 0 := by
      intro i
      exact congrArg (fun y => y.toAdd i)
        ((VectorGroup.coordinates (CommRingCat.of k) n A).apply_symm_apply _)
    simp_rw [hcoord] at hsum
    have hterm : ∀ i, (f i).eval₂ (AdditiveGroupQuotient.structureMap A)
          (if i = j then AffineLine.coord (Spec (CommRingCat.of k)) else 0) =
        if i = j then (f i).eval₂ (AdditiveGroupQuotient.structureMap A)
          (AffineLine.coord (Spec (CommRingCat.of k))) else 0 := by
      intro i
      split_ifs
      · rfl
      · rw [eval₂_at_zero, (hf i).coeff_zero, map_zero]
    simp_rw [hterm] at hsum
    have heval : (f j).eval₂ (AdditiveGroupQuotient.structureMap A)
        (AffineLine.coord (Spec (CommRingCat.of k))) = 0 := by
      simpa only [Finset.sum_ite_eq', Finset.mem_univ, ite_true] using hsum
    apply AdditiveGroupQuotient.bijective_eval₂RingHom_affineLine.injective
    exact heval.trans (map_zero _).symm
  · intro h
    apply hom_ext_points
    intro T x
    rw [comp_polynomialRow, Grp.zero_hom, Mon.zero_hom, ← Hom.one_def, MonObj.comp_one]
    apply VectorGroup.points_ext
    intro j
    rw [polynomialRowPoints_coord]
    simp only [h, Pi.zero_apply, eval₂_zero, Finset.sum_const_zero]
    exact (congrArg (fun y => y.toAdd j)
      (VectorGroup.coordinates (CommRingCat.of k) 1 T).map_one).symm

/-- A nonzero actual row leaves a positive residual coordinate count, hence
the ambient vector factor has strictly smaller coordinate count. -/
theorem polynomialKernelAmbientFactor_rank_lt {n r m : ℕ}
    (f : Fin n → k[X]) (hf : ∀ i, IsAdditive (f i))
    (g : Fin m → k[X]) (hg : ∀ i, IsAdditive (g i))
    (e : VectorGroup.groupScheme (CommRingCat.of k) n ≅
      VectorGroup.groupScheme (CommRingCat.of k) r ⊗
        VectorGroup.groupScheme (CommRingCat.of k) m)
    (he : e.hom ≫ snd _ _ ≫ polynomialRow g hg = polynomialRow f hf)
    (hrm : r + m = n) (hf0 : polynomialRow f hf ≠ 0) : r < n := by
  have hm : m ≠ 0 := by
    intro h
    subst m
    apply hf0
    rw [← he, polynomialRow_zeroVariables]
    simp
  omega

/-- The iterated vector factor can be chosen with a compatible isomorphism of
the ambient vector groups, retaining the actual polynomial-row equation. -/
theorem exists_polynomialKernelAmbientFactor (n : ℕ)
    (f : Fin n → k[X]) (hf : ∀ i, IsAdditive (f i)) :
    ∃ (r m : ℕ) (g : Fin m → k[X]) (hg : ∀ i, IsAdditive (g i)),
      r + m = n ∧ HasConstantAffineLineMaps (kernel (polynomialRow g hg)) ∧
        ∃ e : VectorGroup.groupScheme (CommRingCat.of k) n ≅
            VectorGroup.groupScheme (CommRingCat.of k) r ⊗
              VectorGroup.groupScheme (CommRingCat.of k) m,
          e.hom ≫ snd _ _ ≫ polynomialRow g hg = polynomialRow f hf := by
  induction n with
  | zero =>
    refine ⟨0, 0, f, hf, rfl, hasConstantAffineLineMaps_polynomialKernel_zero f hf,
      (VectorGroup.zeroProductIso _ _).symm, ?_⟩
    simp [VectorGroup.zeroProductIso]
  | succ n ih =>
    by_cases h : HasConstantAffineLineMaps (kernel (polynomialRow f hf))
    · refine ⟨0, n + 1, f, hf, Nat.zero_add _, h,
        (VectorGroup.zeroProductIso _ _).symm, ?_⟩
      simp [VectorGroup.zeroProductIso]
    · obtain ⟨g, hg, e₀, he₀, j, hj⟩ :=
        hasPolynomialKernelZeroCoordinate_of_not_hasConstantAffineLineMaps f hf h
      obtain ⟨r, m, q, hq, hrm, hc, e₁, he₁⟩ :=
        ih (fun i => g (j.succAbove i)) (fun i => hg (j.succAbove i))
      let d := e₀.symm ≪≫ VectorGroup.splitIso (CommRingCat.of k) j
      have hd : d.hom ≫ snd _ _ ≫
          polynomialRow (fun i => g (j.succAbove i)) (fun i => hg (j.succAbove i)) =
            polynomialRow f hf := by
        dsimp [d]
        rw [Category.assoc, splitIso_hom_snd_comp_polynomialRow g hg j hj,
          ← he₀, Iso.inv_hom_id_assoc]
      refine ⟨r + 1, m, q, hq, by omega, hc,
        d ≪≫ (Iso.refl _ ⊗ᵢ e₁) ≪≫ (α_ _ _ _).symm ≪≫
          ((VectorGroup.splitIso (CommRingCat.of k) (0 : Fin (r + 1))).symm ⊗ᵢ
            Iso.refl _), ?_⟩
      simpa only [Iso.trans_hom, Iso.symm_hom, tensorIso_hom, Category.assoc,
        tensorHom_snd_assoc, Iso.refl_hom, Category.id_comp,
        associator_inv_snd_assoc, tensorHom_snd, Category.comp_id, he₁] using hd

/-- The residual kernel in the ambient decomposition remains constant after
actual base change to the separable closure. -/
theorem exists_polynomialKernelAmbientFactor_separableClosure (n : ℕ)
    (f : Fin n → k[X]) (hf : ∀ i, IsAdditive (f i)) :
    ∃ (r m : ℕ) (g : Fin m → k[X]) (hg : ∀ i, IsAdditive (g i)),
      r + m = n ∧ HasConstantAffineLineMaps (kernel (polynomialRow g hg)) ∧
        HasConstantAffineLineMaps
          ((Over.pullback (algebraBaseMap k (SeparableClosure k))).mapGrp.obj
            (kernel (polynomialRow g hg))) ∧
        ∃ e : VectorGroup.groupScheme (CommRingCat.of k) n ≅
            VectorGroup.groupScheme (CommRingCat.of k) r ⊗
              VectorGroup.groupScheme (CommRingCat.of k) m,
          e.hom ≫ snd _ _ ≫ polynomialRow g hg = polynomialRow f hf := by
  obtain ⟨r, m, g, hg, hrm, hc, e, he⟩ := exists_polynomialKernelAmbientFactor n f hf
  exact ⟨r, m, g, hg, hrm, hc,
    (hasConstantAffineLineMaps_baseChange_polynomialKernel_iff g hg).mpr hc, e, he⟩

/-- A nonzero additive row has a compatible ambient factor of strictly smaller
coordinate count, with a residual kernel constant over the separable closure. -/
theorem exists_polynomialKernelAmbientFactor_of_ne_zero (n : ℕ)
    (f : Fin n → k[X]) (hf : ∀ i, IsAdditive (f i)) (hf0 : f ≠ 0) :
    ∃ (r m : ℕ) (g : Fin m → k[X]) (hg : ∀ i, IsAdditive (g i)),
      r + m = n ∧ r < n ∧ HasConstantAffineLineMaps (kernel (polynomialRow g hg)) ∧
        HasConstantAffineLineMaps
          ((Over.pullback (algebraBaseMap k (SeparableClosure k))).mapGrp.obj
            (kernel (polynomialRow g hg))) ∧
        ∃ e : VectorGroup.groupScheme (CommRingCat.of k) n ≅
            VectorGroup.groupScheme (CommRingCat.of k) r ⊗
              VectorGroup.groupScheme (CommRingCat.of k) m,
          e.hom ≫ snd _ _ ≫ polynomialRow g hg = polynomialRow f hf := by
  obtain ⟨r, m, g, hg, hrm, hc, hcs, e, he⟩ :=
    exists_polynomialKernelAmbientFactor_separableClosure n f hf
  exact ⟨r, m, g, hg, hrm,
    polynomialKernelAmbientFactor_rank_lt f hf g hg e he hrm
      (fun h => hf0 ((polynomialRow_eq_zero_iff f hf).mp h)), hc, hcs, e, he⟩

end Langlands.GroupScheme.Unipotent
