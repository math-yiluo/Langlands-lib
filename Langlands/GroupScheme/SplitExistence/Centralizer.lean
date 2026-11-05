import Langlands.GroupScheme.SplitExistence.GeometricPoints
import Langlands.GroupScheme.Dynamic.AffineRepresentability
import Langlands.GroupScheme.Dynamic.ClosedSubgroup
import Langlands.GroupScheme.Dynamic.GeneralLinearProof
import Langlands.GroupScheme.Dynamic.SmoothProof
import Langlands.AlgebraicGeometry.SmoothReducedProof

/-! # The centralizer of the regular cocharacter is the torus

For the Chevalley group `G ⊆ GL_n` over a field `k`, the dynamic centralizer `Z_G(λ)` of the
cocharacter `λ` attached to `ℓ` is the torus `D(X)`, on every test scheme. On geometric points
this is the Tits-system identity `Γ ∩ P_ℓ = B` together with `B ∩ L_ℓ = T`, where `L_ℓ` is the
block Levi subgroup; smoothness of `Z_G(λ)` then gives the scheme-theoretic statement. -/

noncomputable section

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open scoped CategoryTheory.MonObj

namespace Langlands.GroupScheme.SplitExistence

namespace ChevalleyData

variable {J X Y : Type u} [AddCommGroup X] [AddCommGroup Y] {P : RootDatum J X Y} {b : P.Base}
  (D : ChevalleyData P b)

/-- A matrix of `Γ(K)` that is block diagonal for the weights `ℓ(wt c)` lies in `T(K)`. -/
theorem mem_torusSub_of_blockLevi [Finite J] [P.IsReduced] {K : Type u} [Field K]
    {g : GL (Fin D.n) K} (hg : g ∈ D.chevSub K)
    (hl : ∀ c d, D.ℓ (D.wt c) ≠ D.ℓ (D.wt d) → (g : Matrix (Fin D.n) (Fin D.n) K) c d = 0) :
    g ∈ D.torusSub K := by
  have hbt : g ∈ D.btSub K := fun c d hcd =>
    hl c d (ne_of_lt (OrderDual.toDual_lt_toDual.mp hcd))
  have hB : g ∈ D.borelSub K := by
    rw [← D.chevSub_inf_btSub]
    exact ⟨hg, hbt⟩
  obtain ⟨τ, hτ, v, hv, rfl⟩ := mem_borelSub.1 hB
  obtain ⟨χ, rfl⟩ := hτ
  have hut : D.IsUT (v : Matrix (Fin D.n) (Fin D.n) K) := D.posSub_le_utSub hv
  have hentry : ∀ c d, (v : Matrix (Fin D.n) (Fin D.n) K) c d =
      ((χ (Multiplicative.ofAdd (D.wt c)))⁻¹ : Kˣ) *
        ((D.torusHom χ * v : GL (Fin D.n) K) : Matrix (Fin D.n) (Fin D.n) K) c d := by
    intro c d
    rw [Units.val_mul, coe_torusHom, Matrix.diagonal_mul, ← mul_assoc, ← Units.val_mul,
      inv_mul_cancel, Units.val_one, one_mul]
  have hv1 : v = 1 := by
    have hoff : ∀ c d, (v : Matrix (Fin D.n) (Fin D.n) K) c d ≠ 0 →
        c = d ∧ (v : Matrix (Fin D.n) (Fin D.n) K) c d = 1 := by
      intro c d hcd
      rcases hut c d hcd with h | h
      · exact h
      · exfalso
        apply hcd
        rw [hentry, hl c d (ne_of_gt h), mul_zero]
    ext c d
    by_cases hcd : c = d
    · subst hcd
      obtain ⟨c', hc'⟩ := D.exists_entry_ne_zero v c
      obtain ⟨rfl, h1⟩ := hoff c' c hc'
      rw [h1, Units.val_one, Matrix.one_apply_eq]
    · rw [Units.val_one, Matrix.one_apply_ne hcd]
      by_contra h
      exact hcd (hoff c d h).1
  rw [hv1, mul_one]
  exact ⟨χ, rfl⟩

variable (k : Type u) [Field k]

/-- The Chevalley group: a final stage of the construction with the torus and all root
homomorphisms factored through it. -/
structure ChevGroup extends D.Stage k where
  /-- The torus `D(X) → G`. -/
  t : (Tk (X := X) k).toGrp ⟶ H
  t_comp : t ≫ i = D.torusToGL k
  /-- The root homomorphisms `𝔾ₐ → G`. -/
  u : J → (Gak k ⟶ H)
  u_comp : ∀ j, u j ≫ i = D.rootToGL k j

theorem nonempty_chevGroup [Finite J] [Module.Finite ℤ X] : Nonempty (D.ChevGroup k) := by
  obtain ⟨s, hs, hr⟩ := D.exists_chevalley_stage k (isSplitTorus_Tk k P)
  obtain ⟨t, ht⟩ := exists_hom_factor s.i s.closed (D.torusToGL k) hs
  choose u hu using fun j => exists_hom_factor s.i s.closed (D.rootToGL k j) (hr j)
  exact ⟨{ s with t := t, t_comp := ht, u := u, u_comp := hu }⟩

variable {D k}

namespace ChevGroup

variable (G : D.ChevGroup k)

theorem mono_i : Mono G.i.hom.hom := by
  have : IsClosedImmersion G.i.hom.hom.left := G.closed
  exact Over.mono_of_mono_left _

theorem t_closed [Module.Finite ℤ X] : IsClosedSubgroup G.t :=
  IsClosedSubgroup.of_comp G.closed (by
    rw [G.t_comp]
    exact D.isClosedSubgroup_torusToGL k (isSplitTorus_Tk k P))

/-- The regular cocharacter `λ : 𝔾ₘ → G` attached to `ℓ`. -/
def cochar : (Gm (Spec (CommRingCat.of k))).toGrp ⟶ G.H := D.cochar k ≫ G.t

theorem cochar_comp_i :
    G.cochar ≫ G.i = GeneralLinear.diagonalCocharacter (Fin D.n) (CommRingCat.of k)
      D.ellWeights := by
  rw [cochar, Category.assoc, G.t_comp, cochar_comp_torusToGL]

theorem glExt_apply (K : Type u) [Field K] [Algebra k K]
    (x : extPoint (k := k) K ⟶ (D.GLk k).X) (c d : Fin D.n) :
    (D.glExt k K x : Matrix (Fin D.n) (Fin D.n) K) c d =
      specRingEquiv k K ((GeneralLinear.pointsEquiv (Fin D.n) (CommRingCat.of k)
        (extPoint K) x : Matrix (Fin D.n) (Fin D.n) _) c d) :=
  rfl

/-- **The centralizer of the regular cocharacter lies in the torus**, on every test scheme. -/
theorem centralizer_le [Finite J] [P.IsReduced] [Module.Finite ℤ X] :
    Dynamic.centralizer G.cochar ≤ SubgroupFunctor.range G.t := by
  have := G.smooth
  have := G.affine
  have : IsAffine G.H.X.left := isAffine_of_isAffineHom G.H.X.hom
  have hmono := G.mono_i
  let χ := G.cochar
  let z := Dynamic.Affine.centralizerHom χ
  have hz := Dynamic.Affine.isRepresentedBy_centralizerHom χ
  have hzs : Smooth (Dynamic.Affine.centralizerScheme χ).X.hom :=
    (dynamicSmooth k G.H χ _ z).2.1 hz
  have : IsReduced (Dynamic.Affine.centralizerScheme χ).X.left :=
    Langlands.AlgebraicGeometry.SmoothReducedProof.isReduced_of_smooth_over_field k _
      (Dynamic.Affine.centralizerScheme χ).X.hom
  have : LocallyOfFiniteType (Dynamic.Affine.centralizerScheme χ).X.hom := inferInstance
  rw [← hz.2]
  let K := AlgebraicClosure k
  refine range_le_of_extPoints K G.t_closed fun x => ?_
  have hy : x ≫ z.hom.hom ∈ (Dynamic.centralizer χ).carrier (extPoint K) := by
    rw [← hz.2]
    exact ⟨x, rfl⟩
  rw [Dynamic.centralizer_eq_comap_of_isClosedSubgroup χ G.i G.closed,
    SubgroupFunctor.mem_comap, G.cochar_comp_i,
    (GeneralLinear.dynamicStatement.1 (Fin D.n) (CommRingCat.of k) D.ellWeights).2.1,
    GeneralLinear.mem_blockLevi] at hy
  have hpts := G.points K (x ≫ z.hom.hom)
  rw [D.mem_chevPoints_iff_glExt k K] at hpts
  have hT := D.mem_torusSub_of_blockLevi hpts fun c d hcd => by
    rw [glExt_apply, hy c d hcd, map_zero]
  obtain ⟨χ', hχ'⟩ := hT
  let w : extPoint K ⟶ (Tk (X := X) k).toGrp.X := (torusPointsEquiv k (extPoint K)).symm
    ((Units.map (specRingEquiv k K).symm.toRingHom.toMonoidHom).comp χ')
  refine ⟨w, ?_⟩
  apply hmono.right_cancellation
  rw [Category.assoc, ← Grp.comp_hom_hom, G.t_comp]
  apply (D.glExt k K).injective
  rw [← hχ']
  change glMapEquiv (specRingEquiv k K) (GeneralLinear.pointsEquiv (Fin D.n) (CommRingCat.of k)
    (extPoint K) (w ≫ (D.torusToGL k).hom.hom)) = _
  rw [pointsEquiv_torusToGL]
  change Matrix.GeneralLinearGroup.map (specRingEquiv k K).toRingHom (D.torusHom _) = _
  rw [D.torusHom_map, MulEquiv.apply_symm_apply]
  congr 1
  ext m
  simp

end ChevGroup

end ChevalleyData

end Langlands.GroupScheme.SplitExistence
