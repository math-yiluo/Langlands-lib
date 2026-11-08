import Langlands.GroupScheme.SplitExistence.Assembly
import Langlands.GroupScheme.Rational.MonicRootParametrization

/-! # Root maps of a Chevalley group represent the intrinsic root subgroups -/

noncomputable section

set_option backward.isDefEq.respectTransparency false

universe u

open CategoryTheory AlgebraicGeometry Matrix
open scoped CategoryTheory.MonObj

namespace Langlands.GroupScheme.SplitExistence

namespace ChevalleyData

variable {J X Y : Type u} [AddCommGroup X] [AddCommGroup Y] {P : RootDatum J X Y} {b : P.Base}
  (D : ChevalleyData P b)

section Ring

variable {K : Type u} [CommRing K]

/-- An entry of the first divided power records the parameter linearly in the root
exponential. -/
theorem x_apply_of_e_one_ne_zero (j : J) (s : K) {c d : Fin D.n} (h : D.e j 1 c d ≠ 0) :
    (D.x j s : Matrix (Fin D.n) (Fin D.n) K) c d = s * (D.e j 1 c d : K) := by
  have := isTorsionFree_weight P
  rw [coe_x, divExp, Matrix.sum_apply]
  have h1n : 1 ∈ Finset.range (D.n + 1) := by
    have : 0 < D.n := Fin.pos c
    simp only [Finset.mem_range]
    omega
  rw [Finset.sum_eq_single_of_mem 1 h1n]
  · simp [Matrix.smul_apply, Matrix.map_apply]
  · intro k _ hk
    by_cases hk0 : D.e j k c d = 0
    · simp [Matrix.smul_apply, Matrix.map_apply, hk0]
    · exfalso
      have h3 : k • P.root j = 1 • P.root j :=
        add_left_cancel ((D.e_weight j k c d hk0).symm.trans (D.e_weight j 1 c d h))
      have h4 : (k : ℤ) • P.root j = ((1 : ℕ) : ℤ) • P.root j := by
        rw [natCast_zsmul, natCast_zsmul]
        exact h3
      exact hk (by exact_mod_cast smul_left_injective ℤ (P.ne_zero j) h4)

/-- The entries of the first divided power generate the unit ideal of `ℤ`. -/
theorem one_mem_span_e_one (j : J) :
    (1 : ℤ) ∈ Ideal.span (Set.range fun cd : Fin D.n × Fin D.n => D.e j 1 cd.1 cd.2) := by
  set I := Ideal.span (Set.range fun cd : Fin D.n × Fin D.n => D.e j 1 cd.1 cd.2)
  by_contra hI
  obtain ⟨g, hg⟩ := (inferInstance : I.IsPrincipal)
  have hg1 : g.natAbs ≠ 1 := by
    intro h1
    apply hI
    rw [hg]
    rcases Int.natAbs_eq_iff.mp h1 with h | h
    · rw [h]
      exact Submodule.mem_span_singleton.mpr ⟨1, by norm_num⟩
    · rw [h]
      exact Submodule.mem_span_singleton.mpr ⟨-1, by norm_num⟩
  obtain ⟨p, hp, hpg⟩ := Nat.exists_prime_and_dvd hg1
  apply D.e_one_map_ne_zero j p hp
  ext c d
  have hm : D.e j 1 c d ∈ I := Ideal.subset_span ⟨(c, d), rfl⟩
  rw [hg, Submodule.mem_span_singleton] at hm
  obtain ⟨a, ha⟩ := hm
  simp only [Matrix.map_apply, Matrix.zero_apply, Int.coe_castRingHom]
  rw [ZMod.intCast_zmod_eq_zero_iff_dvd, ← ha]
  exact Dvd.dvd.mul_left (Int.natCast_dvd.mpr hpg) a

/-- Root exponentials are injective over every commutative ring. -/
theorem x_injective (j : J) : Function.Injective (D.x j : K → GL (Fin D.n) K) := by
  intro s s' h
  have hz : D.x j (s - s') = 1 := by
    rw [sub_eq_add_neg, x_add, x_neg, h, mul_inv_cancel]
  have hentry : ∀ cd : Fin D.n × Fin D.n, (s - s') * (D.e j 1 cd.1 cd.2 : K) = 0 := by
    rintro ⟨c, d⟩
    by_cases hcd : D.e j 1 c d = 0
    · simp [hcd]
    · rw [← x_apply_of_e_one_ne_zero D j (s - s') hcd, hz]
      have hne : c ≠ d := by
        rintro rfl
        apply P.ne_zero j
        have := D.e_weight j 1 c c hcd
        simpa using this
      simp [Units.val_one, Matrix.one_apply_ne hne]
  let f : ℤ →ₗ[ℤ] K := (AddMonoidHom.mulLeft (s - s')).comp (Int.castAddHom K) |>.toIntLinearMap
  have hle : Ideal.span (Set.range fun cd : Fin D.n × Fin D.n => D.e j 1 cd.1 cd.2) ≤
      LinearMap.ker f := by
    rw [Ideal.span_le]
    rintro _ ⟨cd, rfl⟩
    exact hentry cd
  have h1 := hle (D.one_mem_span_e_one j)
  have h1' : (s - s') * ((1 : ℤ) : K) = 0 := h1
  rw [Int.cast_one, mul_one, sub_eq_zero] at h1'
  exact h1'

end Ring

variable (k : Type u) [Field k]

/-- The root homomorphism of the ambient linear group is a monomorphism. -/
instance mono_rootToGL (j : J) : Mono (D.rootToGL k j).hom.hom := by
  constructor
  intro T x y h
  apply VectorGroup.points_ext
  intro i
  have hxy := congrArg (GeneralLinear.pointsEquiv (Fin D.n) (CommRingCat.of k) T) h
  rw [pointsEquiv_rootToGL, pointsEquiv_rootToGL] at hxy
  have := D.x_injective j hxy
  fin_cases i
  exact this

/-- The coordinate of a scalar point of the additive group is its scalar. -/
theorem gaCoord_scalarPoint (T : Over (Spec (CommRingCat.of k))) (c : Γ(T.left, ⊤)) :
    Multiplicative.toAdd (gaCoord k T (VectorGroup.scalarPoint (CommRingCat.of k) T c)) = c :=
  VectorGroup.coordinates_scalarPoint _ T c 0

/-- The value of the character attached to a weight is the torus point's value. -/
theorem charValue_charOf (ξ : X) (T : Over (Spec (CommRingCat.of k)))
    (t : T ⟶ (Tk (X := X) k).toGrp.X) :
    VectorGroup.charValue (charOf k ξ) T t =
      ((torusPointsEquiv k T t (Multiplicative.ofAdd ξ) : (Γ(T.left, ⊤))ˣ) : Γ(T.left, ⊤)) := by
  rw [VectorGroup.charValue, gmPoints_charOf]

/-- The rational points of `𝔾ₐ` are the elements of the field. -/
def gaRationalEquiv :
    Multiplicative k ≃* (Over.mk (𝟙 (Spec (CommRingCat.of k))) ⟶ (Gak k).X) :=
  (AddEquiv.toMultiplicative
      ((Scheme.ΓSpecIso (CommRingCat.of k)).commRingCatIsoToRingEquiv.symm.toAddEquiv.trans
        (AddEquiv.piUnique fun _ : Fin 1 =>
          Γ((Over.mk (𝟙 (Spec (CommRingCat.of k)))).left, ⊤)).symm)).trans
    (VectorGroup.coordinates (CommRingCat.of k) 1 _).symm

/-- The coordinate of the rational point attached to a field element. -/
theorem gaCoord_gaRationalEquiv (s : Multiplicative k) :
    Multiplicative.toAdd (gaCoord k _ (gaRationalEquiv k s)) =
      (Scheme.ΓSpecIso (CommRingCat.of k)).inv (Multiplicative.toAdd s) := by
  simp only [gaRationalEquiv, gaCoord, MonoidHom.coe_comp, MulEquiv.coe_toMonoidHom,
    Function.comp_apply, MulEquiv.trans_apply, MulEquiv.apply_symm_apply]
  rfl

variable {D k}

namespace ChevGroup

variable (G : D.ChevGroup k)

/-- The root homomorphisms of a Chevalley group are monomorphisms. -/
instance mono_u (j : J) : Mono (G.u j).hom.hom := by
  have h : (G.u j).hom.hom ≫ G.i.hom.hom = (D.rootToGL k j).hom.hom := by
    rw [← G.u_comp j]
    rfl
  have : Mono ((G.u j).hom.hom ≫ G.i.hom.hom) := by
    rw [h]
    infer_instance
  exact mono_of_mono _ G.i.hom.hom

/-- Conjugation by torus points scales the root parameter on every test scheme. -/
theorem u_isTorusEquivariant (j : J) :
    VectorGroup.IsTorusEquivariant G.t (G.u j) (charOf k (P.root j)) := by
  intro Z t c
  have hm := G.mono_i
  apply hm.right_cancellation
  rw [MonObj.mul_comp, MonObj.mul_comp, GrpObj.inv_comp]
  have ht : (t ≫ G.t.hom.hom) ≫ G.i.hom.hom = t ≫ (D.torusToGL k).hom.hom := by
    rw [Category.assoc, ← G.t_comp]
    rfl
  have hu : ∀ c' : Γ(Z.left, ⊤),
      (VectorGroup.scalarPoint (CommRingCat.of k) Z c' ≫ (G.u j).hom.hom) ≫ G.i.hom.hom =
        VectorGroup.scalarPoint (CommRingCat.of k) Z c' ≫ (D.rootToGL k j).hom.hom := by
    intro c'
    rw [Category.assoc, ← G.u_comp j]
    rfl
  rw [ht, hu, hu]
  apply (GeneralLinear.pointsEquiv (Fin D.n) (CommRingCat.of k) Z).injective
  rw [map_mul, map_mul, map_inv, pointsEquiv_torusToGL, pointsEquiv_rootToGL,
    pointsEquiv_rootToGL, gaCoord_scalarPoint, gaCoord_scalarPoint, torusHom_conj_x,
    charValue_charOf]

variable [Finite J] [P.IsReduced] [Module.Finite ℤ X] [Module.Free ℤ X]

omit [Module.Free ℤ X] in
/-- No integral multiple of at least two of a root of a reduced root datum is a root of
the Chevalley group. -/
theorem hasNoHigherRoots_charOf [IsAffine G.H.X.left] [LocallyOfFiniteType G.H.X.hom]
    [Module.Free ℤ X] (j : J) :
    RelativeRoot.HasNoHigherRoots G.t (charOf k (P.root j)) := by
  have := isTorsionFree_weight P
  intro n hn hmem
  rw [relativeRoots, G.roots_t] at hmem
  obtain ⟨j', hj'⟩ := hmem
  simp only at hj'
  have he : P.root j' = n • P.root j := by
    apply (charEquiv k (X := X)).injective
    rw [charEquiv_apply, charEquiv_apply, hj']
    exact (map_nsmul (charOfHom k) n (P.root j)).symm
  have hdep : ¬ LinearIndependent ℤ ![P.root j', P.root j] := by
    intro hli
    have := LinearIndependent.pair_iff.mp hli 1 (-(n : ℤ)) (by
      rw [he, one_smul, neg_smul, natCast_zsmul, add_neg_cancel])
    exact one_ne_zero this.1
  rcases RootPairing.IsReduced.eq_or_eq_neg (P := P) j' j hdep with h | h
  · rw [he] at h
    have h4 : (n : ℤ) • P.root j = ((1 : ℕ) : ℤ) • P.root j := by
      rw [natCast_zsmul, natCast_zsmul, one_smul]
      exact h
    have := smul_left_injective ℤ (P.ne_zero j) h4
    omega
  · rw [he] at h
    have h4 : (n : ℤ) • P.root j = (-1 : ℤ) • P.root j := by
      rw [natCast_zsmul, neg_one_smul]
      exact h
    have := smul_left_injective ℤ (P.ne_zero j) h4
    omega

/-- **Root subgroups of a Chevalley group.** Each root homomorphism represents the entire
intrinsic root subgroup of the corresponding character on every test scheme. -/
theorem represents_root [IsAffine G.H.X.left] [LocallyOfFiniteType G.H.X.hom] (j : J) :
    (RelativeRoot.subgroup G.t (charOf k (P.root j))).IsRepresentedBy (G.u j) := by
  have : IsAffineHom G.H.X.hom := G.affine
  have hα : charOf k (P.root j) ∈ roots G.t := by
    rw [G.roots_t]
    exact ⟨j, rfl⟩
  exact (G.u_isTorusEquivariant j).represents_root G.isConnectedReductive (isSplitTorus_Tk k P)
    G.isMaximalTorus hα (G.hasNoHigherRoots_charOf j)

/-- The rational points of the intrinsic root subgroup are the rational points of `𝔾ₐ`
under the root homomorphism. -/
def rootPointsEquiv [IsAffine G.H.X.left] [LocallyOfFiniteType G.H.X.hom] (j : J) :
    (Over.mk (𝟙 (Spec (CommRingCat.of k))) ⟶ (Gak k).X) ≃*
      (RelativeRoot.subgroup G.t (charOf k (P.root j))).carrier
        (Over.mk (𝟙 (Spec (CommRingCat.of k)))) :=
  (G.represents_root j).pointsEquiv _

/-- Field coordinates on the rational points of a root subgroup of a Chevalley group. -/
def rootCoordEquiv [IsAffine G.H.X.left] [LocallyOfFiniteType G.H.X.hom] (j : J) :
    Multiplicative k ≃*
      (RelativeRoot.subgroup G.t (charOf k (P.root j))).carrier
        (Over.mk (𝟙 (Spec (CommRingCat.of k)))) :=
  (gaRationalEquiv k).trans (G.rootPointsEquiv j)

theorem rootCoordEquiv_apply_coe [IsAffine G.H.X.left] [LocallyOfFiniteType G.H.X.hom]
    (j : J) (s : Multiplicative k) :
    (G.rootCoordEquiv j s : Over.mk (𝟙 (Spec (CommRingCat.of k))) ⟶ G.H.X) =
      gaRationalEquiv k s ≫ (G.u j).hom.hom :=
  rfl

end ChevGroup

end ChevalleyData

end Langlands.GroupScheme.SplitExistence
