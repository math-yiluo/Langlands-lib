import Langlands.GroupScheme.Dynamic.AffineChart
import Langlands.GroupScheme.Torus.Lattice

/-! # Opposite dynamic intersections for affine group schemes -/

noncomputable section

universe u

open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory
open CategoryTheory.CartesianMonoidalCategory AlgebraicGeometry
open scoped CategoryTheory.MonObj

namespace Langlands.GroupScheme

namespace Dynamic

variable {B : Scheme.{u}} {G : GroupScheme B}

/-- The cocharacter obtained by inverting the Gm parameter. -/
def oppositeCocharacter (χ : (Gm B).toGrp ⟶ G) : (Gm B).toGrp ⟶ G :=
  CommGroupScheme.groupHom (Gm.powerHom B (-1)) ≫ χ

theorem orbit_oppositeCocharacter (χ : (Gm B).toGrp ⟶ G) {U : Over B}
    (g : U ⟶ G.X) :
    orbit (oppositeCocharacter χ) g =
      U ◁ (CommGroupScheme.groupHom (Gm.powerHom B (-1))).hom.hom ≫ orbit χ g := by
  simp only [oppositeCocharacter, orbit, Grp.comp_hom_hom, MonObj.comp_mul,
    GrpObj.comp_inv, whiskerLeft_snd_assoc, whiskerLeft_fst_assoc]

end Dynamic

namespace AffineLine

variable {B : Scheme.{u}} {A : CommRingCat.{u}} (f : Spec A ⟶ B)

/-- Inversion of the Laurent variable as an actual ring endomorphism. -/
abbrev laurentInvertRing :
    CommRingCat.of (LaurentPolynomial A) ⟶ CommRingCat.of (LaurentPolynomial A) :=
  CommRingCat.ofHom LaurentPolynomial.invert.toRingHom

theorem polynomialC_comp_polynomialToLaurent_comp_invert :
    polynomialC A ≫ polynomialToLaurent A ≫ laurentInvertRing =
      polynomialC A ≫ polynomialToLaurent A := by
  apply CommRingCat.hom_ext
  apply RingHom.ext
  intro a
  change LaurentPolynomial.invert (Polynomial.toLaurent (Polynomial.C a)) =
    Polynomial.toLaurent (Polynomial.C a)
  rw [Polynomial.toLaurent_C, LaurentPolynomial.invert_C]

/-- Inversion of the Laurent variable preserves the structural map through Spec A. -/
def laurentInvert : laurentScheme f ⟶ laurentScheme f :=
  Over.homMk (Spec.map laurentInvertRing) (by
    change Spec.map laurentInvertRing ≫ Spec.map (polynomialToLaurent A) ≫
      Spec.map (polynomialC A) ≫ f =
      Spec.map (polynomialToLaurent A) ≫ Spec.map (polynomialC A) ≫ f
    simp only [← Spec.map_comp_assoc]
    simpa only [Category.assoc] using congrArg (fun r => Spec.map r ≫ f)
      (polynomialC_comp_polynomialToLaurent_comp_invert (A := A)))

theorem laurentInvert_comp_laurentPoint :
    laurentInvert f ≫ laurentPoint f =
      laurentPoint f ≫ Over.mk f ◁
        (CommGroupScheme.groupHom (Gm.powerHom B (-1))).hom.hom := by
  apply CartesianMonoidalCategory.hom_ext
  · simp only [Category.assoc, laurentPoint, lift_fst,
      whiskerLeft_fst]
    apply Over.OverMorphism.ext
    change Spec.map laurentInvertRing ≫ Spec.map (polynomialToLaurent A) ≫
      Spec.map (polynomialC A) =
      Spec.map (polynomialToLaurent A) ≫ Spec.map (polynomialC A)
    simp only [← Spec.map_comp]
    simpa only [Category.assoc] using congrArg Spec.map
      (polynomialC_comp_polynomialToLaurent_comp_invert (A := A))
  · simp only [Category.assoc, laurentPoint, lift_snd, lift_snd_assoc, whiskerLeft_snd]
    apply (Gm.pointsEquiv B _).injective
    rw [Gm.pointsEquiv_naturality, MulEquiv.apply_symm_apply,
      Gm.powerHom_apply, Gm.comp_zsmul_id, map_zpow, zpow_neg_one,
      MulEquiv.apply_symm_apply]
    apply Units.ext
    change (Spec.map laurentInvertRing).appTop
        ((Scheme.ΓSpecIso _).inv (LaurentPolynomial.T 1)) =
      ((Scheme.ΓSpecIso _).inv (LaurentPolynomial.T (-1)))
    rw [← CommRingCat.comp_apply, ← Scheme.ΓSpecIso_inv_naturality,
      CommRingCat.comp_apply]
    exact congrArg (Scheme.ΓSpecIso _).inv (LaurentPolynomial.invert_T 1)

/-- A polynomial whose Laurent expansion is the inverse-variable expansion of
another polynomial is constant. -/
theorem polynomial_eq_C_eval_zero_of_invert {p q : Polynomial A}
    (h : Polynomial.toLaurent q = LaurentPolynomial.invert (Polynomial.toLaurent p)) :
    q = Polynomial.C (q.eval 0) := by
  apply Polynomial.ext
  intro n
  cases n with
  | zero => simp [Polynomial.coeff_zero_eq_eval_zero]
  | succ n =>
      have hn : -((n + 1 : ℕ) : ℤ) < 0 := by omega
      have hc := congrArg (fun r : LaurentPolynomial A => r.coeff (n + 1 : ℕ)) h
      rw [coeff_toLaurent_natCast, LaurentPolynomial.invert_apply,
        coeff_toLaurent_of_neg _ hn] at hc
      simpa using hc

end AffineLine

namespace Dynamic

open AffineLine AffineChart

variable {R : CommRingCat.{u}} {G : GroupScheme (Spec R)} [IsAffine G.X.left]
  (χ : (Gm (Spec R)).toGrp ⟶ G)

/-- On an affine test scheme, a point contracted by the opposite cocharacter
and admitting a limit under the original cocharacter is the identity. -/
theorem eq_one_of_mem_opposite_unipotent_of_mem_parabolic_affine
    {A : CommRingCat.{u}} {f : Spec A ⟶ Spec R} {g : Over.mk f ⟶ G.X}
    (hminus : g ∈ (unipotent (oppositeCocharacter χ)).carrier (Over.mk f))
    (hplus : g ∈ (parabolic χ).carrier (Over.mk f)) : g = 1 := by
  obtain ⟨en, hen, hen0⟩ := hminus
  obtain ⟨ep, hep⟩ := hplus
  let En := polynomialPoint f ≫ en
  let Ep := polynomialPoint f ≫ ep
  have hn : laurentInclusion f ≫ En =
      laurentPoint f ≫ orbit (oppositeCocharacter χ) g :=
    laurentInclusion_comp_of_whiskerLeft f hen
  have hp : laurentInclusion f ≫ Ep = laurentPoint f ≫ orbit χ g :=
    laurentInclusion_comp_of_whiskerLeft f hep
  have hL : laurentInclusion f ≫ En =
      laurentInvert f ≫ (laurentInclusion f ≫ Ep) := by
    rw [hn, hp, ← Category.assoc, laurentInvert_comp_laurentPoint,
      Category.assoc, ← orbit_oppositeCocharacter]
  have hθ : pointRing En ≫ polynomialToLaurent A =
      pointRing Ep ≫ polynomialToLaurent A ≫ laurentInvertRing := by
    have h := congrArg pointRing hL
    simp only [pointRing_comp] at h
    change pointRing En ≫ Spec.preimage (Spec.map (polynomialToLaurent A)) =
      (pointRing Ep ≫ Spec.preimage (Spec.map (polynomialToLaurent A))) ≫
        Spec.preimage (Spec.map laurentInvertRing) at h
    simpa only [Spec.preimage_map, Category.assoc] using h
  have hconst (b : Γ(G.X.left, ⊤)) :
      pointRing En b = Polynomial.C ((pointRing En b).eval 0) := by
    apply polynomial_eq_C_eval_zero_of_invert
    exact congrArg (fun φ => φ b) hθ
  have hz : polynomialZero f ≫ En = (1 : Over.mk f ⟶ G.X) := by
    dsimp only [En]
    rw [← Category.assoc, polynomialZero_comp_polynomialPoint]
    exact hen0
  have hzRing : pointRing En ≫ polynomialEvalZero A =
      pointRing (1 : Over.mk f ⟶ G.X) := by
    have h := congrArg pointRing hz
    rwa [pointRing_polynomialZero_comp] at h
  have heConst : En = polynomialProj f ≫ (1 : Over.mk f ⟶ G.X) := by
    apply hom_ext_of_pointRing
    rw [pointRing_comp]
    change pointRing En = pointRing (1 : Over.mk f ⟶ G.X) ≫
      Spec.preimage (Spec.map (polynomialC A))
    rw [Spec.preimage_map, ← hzRing]
    exact CommRingCat.hom_ext (RingHom.ext hconst)
  have heN : en = 1 := by
    calc
      en = polynomialPointInv f ≫ En := by
        dsimp only [En]
        rw [← Category.assoc, polynomialPointInv_comp_polynomialPoint, Category.id_comp]
      _ = 1 := by rw [heConst, MonObj.comp_one, MonObj.comp_one]
  have heOrbit : (1 : Over.mk f ⊗ (Gm (Spec R)).X ⟶ G.X) =
      orbit (oppositeCocharacter χ) g := by
    simpa only [IsOrbitExtension, heN, MonObj.comp_one] using hen
  have h := congrArg (lift (𝟙 (Over.mk f)) (1 : Over.mk f ⟶ (Gm (Spec R)).X) ≫ ·) heOrbit
  simpa only [MonObj.comp_one, orbit, MonObj.comp_mul, GrpObj.comp_inv,
    lift_snd_assoc, lift_fst_assoc, MonObj.one_comp, inv_one, one_mul, mul_one,
    Category.id_comp] using h.symm

/-- The opposite dynamic unipotent and the original dynamic parabolic meet
only at the identity, on an arbitrary test scheme. -/
theorem eq_one_of_mem_opposite_unipotent_of_mem_parabolic
    {U : Over (Spec R)} {g : U ⟶ G.X}
    (hminus : g ∈ (unipotent (oppositeCocharacter χ)).carrier U)
    (hplus : g ∈ (parabolic χ).carrier U) : g = 1 := by
  apply Over.OverMorphism.ext
  refine Scheme.Cover.hom_ext U.left.affineOpenCover.openCover _ _ fun j => ?_
  let a : Over.mk (U.left.affineOpenCover.f j ≫ U.hom) ⟶ U :=
    Over.homMk (U.left.affineOpenCover.f j) rfl
  have h : a ≫ g = a ≫ (1 : U ⟶ G.X) :=
    (eq_one_of_mem_opposite_unipotent_of_mem_parabolic_affine χ
      ((unipotent (oppositeCocharacter χ)).comp_mem a hminus)
      ((parabolic χ).comp_mem a hplus)).trans (MonObj.comp_one a).symm
  exact congrArg (fun z => z.left) h

/-- The all-test opposite intersection is trivial for every affine group scheme
over an affine base, without smoothness or reductivity. -/
theorem opposite_unipotent_inf_parabolic :
    unipotent (oppositeCocharacter χ) ⊓ parabolic χ = ⊥ := by
  apply SubgroupFunctor.ext
  intro U
  apply Subgroup.ext
  intro g
  change (g ∈ (unipotent (oppositeCocharacter χ)).carrier U ∧
    g ∈ (parabolic χ).carrier U) ↔ g = 1
  constructor
  · exact fun h => eq_one_of_mem_opposite_unipotent_of_mem_parabolic χ h.1 h.2
  · rintro rfl
    exact ⟨Subgroup.one_mem _, Subgroup.one_mem _⟩

end Dynamic

end Langlands.GroupScheme
