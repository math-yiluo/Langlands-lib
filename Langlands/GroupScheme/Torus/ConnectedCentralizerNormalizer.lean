import Langlands.GroupScheme.Torus.ConnectedPointedHomFamily
import Langlands.GroupScheme.Rational.TorusNormalizer
import Mathlib.GroupTheory.Commutator.Basic

/-! # Connected normalizers of subgroups containing a central diagonalizable group -/

noncomputable section

universe u

open CategoryTheory Opposite AlgebraicGeometry
open CategoryTheory.MonoidalCategory CategoryTheory.CartesianMonoidalCategory
open scoped CategoryTheory.MonObj commutatorElement

namespace Langlands.GroupScheme

open CentralSurjectionImage

set_option backward.isDefEq.respectTransparency false

variable {k : Type u} [Field k]
  {G H : GroupScheme (Spec (CommRingCat.of k))}
  [IsAffine G.X.left] [IsAffine H.X.left] [ConnectedSpace H.X.left]
  {Λ : Type u} [AddCommGroup Λ]

/-- Affine points of a connected group normalizing a subgroup containing a
central diagonalizable group commute with that diagonalizable group. -/
theorem affine_commute_of_connected_normalizer_diagonalizable
    (i : Dg (k := k) Λ ⟶ G) (F : SubgroupFunctor G)
    (hi : SubgroupFunctor.range i ≤ F) (hF : F ≤ torusCentralizer i)
    (h : H ⟶ G) (hn : SubgroupFunctor.range h ≤ F.normalizer)
    (A₀ : Type u) [CommRing A₀] [Algebra k A₀]
    (y₀ : Lie.AffinePoints H A₀) (x₀ : Lie.AffinePoints (Dg (k := k) Λ) A₀) :
    Commute (y₀ ≫ h.hom.hom) (x₀ ≫ i.hom.hom) := by
  let β : ∀ (A : Type u) [CommRing A] [Algebra k A],
      Lie.AffinePoints H A → (Multiplicative Λ →* Aˣ) → Lie.AffinePoints G A :=
    fun A _ _ y x => ⁅y ≫ h.hom.hom, (chi.symm x) ≫ i.hom.hom⁆
  have hnat : ∀ (A B : Type u) [CommRing A] [Algebra k A] [CommRing B] [Algebra k B]
      (f : A →ₐ[k] B) (y : Lie.AffinePoints H A) (x : Multiplicative Λ →* Aˣ),
      Lie.affineMap G f (β A y x) =
        β B (Lie.affineMap H f y) ((Units.map f.toMonoidHom).comp x) := by
    intro A B _ _ _ _ f y x
    dsimp only [β]
    rw [map_commutatorElement]
    congr 1
    rw [Lie.affineMap_apply, ← Category.assoc, ← Lie.affineMap_apply,
      chi_symm_affineMap]
  have hmul : ∀ (A : Type u) [CommRing A] [Algebra k A]
      (y : Lie.AffinePoints H A) (x x' : Multiplicative Λ →* Aˣ),
      β A y (x * x') = β A y x * β A y x' := by
    intro A _ _ y x x'
    dsimp only [β]
    rw [map_mul, MonObj.mul_comp, commutatorElement_mul_right_eq_mul_conj]
    have hy : y ≫ h.hom.hom ∈ F.normalizer.carrier _ := hn _ ⟨y, rfl⟩
    have hx' : (chi.symm x') ≫ i.hom.hom ∈ F.carrier _ := hi _ ⟨_, rfl⟩
    have hconj := SubgroupFunctor.conj_mem_of_mem_normalizer hy hx'
    have hc₁ : Commute ((chi.symm x) ≫ i.hom.hom)
        ((y ≫ h.hom.hom) * ((chi.symm x') ≫ i.hom.hom) * (y ≫ h.hom.hom)⁻¹) := by
      have hc₀ := hF _ hconj _ (𝟙 _) (chi.symm x)
      simpa only [Category.id_comp] using hc₀.symm
    have hc₂ : Commute ((chi.symm x) ≫ i.hom.hom) (((chi.symm x') ≫ i.hom.hom)⁻¹) := by
      apply Commute.inv_right
      exact (Commute.all (chi.symm x) (chi.symm x')).map
        (GroupScheme.affinePointsTarget _ i (CommAlgCat.of (CommRingCat.of k) A))
    have hc : Commute ((chi.symm x) ≫ i.hom.hom)
        ⁅y ≫ h.hom.hom, (chi.symm x') ≫ i.hom.hom⁆ := hc₁.mul_right hc₂
    rw [mul_assoc _ _ ⁅y ≫ h.hom.hom, (chi.symm x') ≫ i.hom.hom⁆, hc.eq]
    simp only [mul_assoc, mul_inv_cancel, mul_one]
  have hone : ∀ (A : Type u) [CommRing A] [Algebra k A]
      (x : Multiplicative Λ →* Aˣ), β A 1 x = 1 := by
    intro A _ _ x
    dsimp only [β]
    rw [MonObj.one_comp]
    simp
  have hb := eq_one_of_connected_pointed_family β hnat hmul hone A₀ y₀ (chi x₀)
  dsimp only [β] at hb
  rw [MulEquiv.symm_apply_apply] at hb
  exact commutatorElement_eq_one_iff_commute.mp hb

/-- A connected affine group normalizing a subgroup functor that contains a
central diagonalizable group centralizes it on all test schemes. -/
theorem range_le_torusCentralizer_of_connected_normalizer_diagonalizable
    (i : Dg (k := k) Λ ⟶ G) (F : SubgroupFunctor G)
    (hi : SubgroupFunctor.range i ≤ F) (hF : F ≤ torusCentralizer i)
    (h : H ⟶ G) (hn : SubgroupFunctor.range h ≤ F.normalizer) :
    SubgroupFunctor.range h ≤ torusCentralizer i := by
  have : IsAffine (Dg (k := k) Λ).X.left :=
    inferInstanceAs (IsAffine (Spec (CommRingCat.of (AddMonoidAlgebra (CommRingCat.of k) Λ))))
  let P := H.X ⊗ (Dg (k := k) Λ).X
  have hp : (algSpec (CommRingCat.of k)).essImage P := by
    rw [essImage_algSpec]
    change IsAffine (Limits.pullback _ _)
    infer_instance
  let e := hp.getIso
  have hu : Commute (fst H.X (Dg (k := k) Λ).X ≫ h.hom.hom)
      (snd H.X (Dg (k := k) Λ).X ≫ i.hom.hom) := by
    change _ * _ = _ * _
    apply (cancel_epi e.hom).mp
    have hc := affine_commute_of_connected_normalizer_diagonalizable i F hi hF h hn
      hp.witness.unop (e.hom ≫ fst _ _) (e.hom ≫ snd _ _)
    simpa only [MonObj.comp_mul, Category.assoc] using hc.eq
  intro U z hz
  obtain ⟨y, rfl⟩ := SubgroupFunctor.mem_range.mp hz
  intro V a t
  have hc := congrArg (fun q => lift (a ≫ y) t ≫ q) hu.eq
  change _ * _ = _ * _
  simpa only [MonObj.comp_mul, lift_fst_assoc, lift_snd_assoc, Category.assoc] using hc

/-- The same connected-normalizer rigidity holds for any split torus. -/
theorem range_le_torusCentralizer_of_connected_normalizer_splitTorus
    {T : CommGroupScheme (Spec (CommRingCat.of k))}
    (i : T.toGrp ⟶ G) (hT : IsSplitTorus T.toGrp) (F : SubgroupFunctor G)
    (hi : SubgroupFunctor.range i ≤ F) (hF : F ≤ torusCentralizer i)
    (h : H ⟶ G) (hn : SubgroupFunctor.range h ≤ F.normalizer) :
    SubgroupFunctor.range h ≤ torusCentralizer i := by
  classical
  obtain ⟨I, hI, ⟨f⟩⟩ := hT
  let : Finite I := hI
  let : Fintype I := Fintype.ofFinite I
  let e : Dg (k := k) (I → ℤ) ≅ T.toGrp :=
    Diagonalizable.splitIso (CommRingCat.of k) (AddEquiv.refl (I → ℤ)) ≪≫ f.symm
  let j := e.hom ≫ i
  have hj : SubgroupFunctor.range j ≤ F := by
    intro U z hz
    obtain ⟨t, rfl⟩ := SubgroupFunctor.mem_range.mp hz
    apply hi U
    apply SubgroupFunctor.mem_range.mpr
    exact ⟨t ≫ e.hom.hom.hom, by simp only [j, Grp.comp_hom_hom, Category.assoc]⟩
  have hFj : F ≤ torusCentralizer j := by
    intro U z hz V a t
    have hc := hF U hz V a (t ≫ e.hom.hom.hom)
    simpa only [j, Grp.comp_hom_hom, Category.assoc] using hc
  have hc := range_le_torusCentralizer_of_connected_normalizer_diagonalizable j F hj hFj h hn
  intro U z hz V a t
  have ht := hc U hz V a (t ≫ e.inv.hom.hom)
  have he : e.inv.hom.hom ≫ j.hom.hom = i.hom.hom := by
    dsimp only [j]
    rw [← Grp.comp_hom_hom, Iso.inv_hom_id_assoc]
  simpa only [Category.assoc, he] using ht

end Langlands.GroupScheme
