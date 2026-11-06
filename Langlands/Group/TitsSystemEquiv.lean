import Langlands.Group.TitsSystemImage

/-! # Tits-system data under multiplicative equivalences -/

noncomputable section

namespace Langlands.Group.TitsSystem

universe u v w

variable {H : Type u} [Group H] {H' : Type v} [Group H']
  {W : Type w} [Group W]
  (e : H ≃* H') (N : Subgroup H) (N' : Subgroup H')
  (hN : N.map e.toMonoidHom = N')

/-- The restriction of the ambient equivalence to the entire corresponding normalizers. -/
def equivNormalizer : N ≃* N' :=
  (e.subgroupMap N).trans (MulEquiv.subgroupCongr hN)

@[simp] theorem equivNormalizer_coe (n : N) :
    (equivNormalizer e N N' hN n : H') = e n := rfl

/-- The same Weyl projection, reparametrized by the normalizer equivalence. -/
def equivProjection (π : N →* W) : N' →* W :=
  π.comp (equivNormalizer e N N' hN).symm.toMonoidHom

@[simp] theorem equivProjection_apply (π : N →* W) (n : N) :
    equivProjection e N N' hN π (equivNormalizer e N N' hN n) = π n := by
  change π ((equivNormalizer e N N' hN).symm
    (equivNormalizer e N N' hN n)) = π n
  rw [MulEquiv.symm_apply_apply]

variable (B : Subgroup H) (π : N →* W)

/-- A multiplicative equivalence transports the Tits axioms, with the same Weyl group. -/
theorem isTitsSystem_equiv {S : Set W} (h : IsTitsSystem B N π S) :
    IsTitsSystem (B.map e.toMonoidHom) N' (equivProjection e N N' hN π) S := by
  subst N'
  apply h.map e.toMonoidHom e.surjective (by
    intro x hx
    have hx' : x = 1 := e.injective (by simpa using hx)
    simpa only [hx'] using (B ⊓ N).one_mem) _
  intro n
  exact equivProjection_apply e N _ rfl π n

include hN in
/-- Saturation transports to the entire two image subgroups. -/
theorem isSaturated_equiv (h : IsSaturated B N) :
    IsSaturated (B.map e.toMonoidHom) N' := by
  rw [← hN]
  apply h.map e.toMonoidHom e.surjective
  · intro x hx
    have hx' : x = 1 := e.injective (by simpa using hx)
    simpa only [hx'] using B.one_mem
  · intro x hx
    have hx' : x = 1 := e.injective (by simpa using hx)
    simpa only [hx'] using N.one_mem

/-- Every Bruhat cell has exactly the image prescribed by the equivalence. -/
theorem image_cell_equiv (w : W) :
    e '' cell B π w = cell (B.map e.toMonoidHom) (equivProjection e N N' hN π) w := by
  subst N'
  exact image_cell e.toMonoidHom _ (equivProjection_apply e N _ rfl π) w

/-- Standard parabolic subsets, for every type, have exactly the transported image. -/
theorem image_standardParabolic_equiv (X : Set W) :
    e '' standardParabolic B π X =
      standardParabolic (B.map e.toMonoidHom) (equivProjection e N N' hN π) X := by
  ext y
  constructor
  · rintro ⟨x, ⟨w, hw, hx⟩, rfl⟩
    exact ⟨w, hw, (image_cell_equiv e N N' hN B π w).le ⟨x, hx, rfl⟩⟩
  · rintro ⟨w, hw, hy⟩
    obtain ⟨x, hx, rfl⟩ := (image_cell_equiv e N N' hN B π w).ge hy
    exact ⟨x, ⟨w, hw, hx⟩, rfl⟩

/-- Conjugate standard parabolics retain both the conjugating element and the type. -/
theorem image_conjStandardParabolic_equiv (g : H) (X : Set W) :
    e '' conjStandardParabolic B π g X =
      conjStandardParabolic (B.map e.toMonoidHom)
        (equivProjection e N N' hN π) (e g) X := by
  rw [conjStandardParabolic, conjStandardParabolic,
    ← image_standardParabolic_equiv e N N' hN B π, Set.image_image, Set.image_image]
  congr 1
  funext x
  simp only [map_mul, map_inv]

/-- Admissibility is preserved and reflected for every subgroup, with unchanged type data. -/
theorem isAdmissibleParabolic_map_equiv_iff (S : Set W) (Q : Subgroup H) :
    IsAdmissibleParabolic (B.map e.toMonoidHom) (equivProjection e N N' hN π) S
      (Q.map e.toMonoidHom) ↔ IsAdmissibleParabolic B π S Q := by
  constructor
  · rintro ⟨g', X, hX, hQ⟩
    obtain ⟨g, rfl⟩ := e.surjective g'
    refine ⟨g, X, hX, e.injective.image_injective ?_⟩
    rw [image_conjStandardParabolic_equiv e N N' hN B π]
    exact hQ
  · rintro ⟨g, X, hX, hQ⟩
    refine ⟨e g, X, hX, ?_⟩
    change e '' (Q : Set H) = _
    rw [hQ, image_conjStandardParabolic_equiv e N N' hN B π]

/-- Each restricted apartment is precisely the image of all its subgroup-valued facets. -/
theorem image_restrictedApartment_equiv (S : Set W) (g : H) :
    (fun Q : Subgroup H => Q.map e.toMonoidHom) '' restrictedApartment B π S g =
      restrictedApartment (B.map e.toMonoidHom) (equivProjection e N N' hN π) S (e g) := by
  ext Q'
  constructor
  · rintro ⟨Q, ⟨n, X, hX, hQ⟩, rfl⟩
    refine ⟨equivNormalizer e N N' hN n, X, hX, ?_⟩
    change e '' (Q : Set H) = _
    rw [hQ, image_conjStandardParabolic_equiv e N N' hN B π, map_mul]
    rfl
  · rintro ⟨n', X, hX, hQ'⟩
    obtain ⟨n, rfl⟩ := (equivNormalizer e N N' hN).surjective n'
    let Q := Q'.comap e.toMonoidHom
    have hQ : Q.map e.toMonoidHom = Q' :=
      Subgroup.map_comap_eq_self_of_surjective e.surjective Q'
    refine ⟨Q, ⟨n, X, hX, e.injective.image_injective ?_⟩, hQ⟩
    change (Q.map e.toMonoidHom : Set H') = _
    rw [hQ, image_conjStandardParabolic_equiv e N N' hN B π, map_mul]
    exact hQ'

/-- The full sets of restricted apartments correspond under subgroup image. -/
theorem image_restrictedApartments_equiv (S : Set W) :
    (fun Qs : Set (Subgroup H) => (fun Q => Q.map e.toMonoidHom) '' Qs) ''
      restrictedApartments B π S =
      restrictedApartments (B.map e.toMonoidHom) (equivProjection e N N' hN π) S := by
  ext Qs
  constructor
  · rintro ⟨_, ⟨g, rfl⟩, rfl⟩
    exact ⟨e g, (image_restrictedApartment_equiv e N N' hN B π S g).symm⟩
  · rintro ⟨g', rfl⟩
    obtain ⟨g, rfl⟩ := e.surjective g'
    exact ⟨_, ⟨g, rfl⟩, image_restrictedApartment_equiv e N N' hN B π S g⟩

end Langlands.Group.TitsSystem
