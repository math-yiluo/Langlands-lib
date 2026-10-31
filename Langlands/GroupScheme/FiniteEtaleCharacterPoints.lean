import Langlands.AlgebraicGeometry.FiniteEtale.GeometricGaloisFiberFunctorProof
import Langlands.AlgebraicGeometry.FiniteEtale.GeometricFiberFiniteProof
import Langlands.GroupScheme.MuFiniteEtaleProof
import Langlands.GroupScheme.Cartier.Characters

/-! # Characters of finite étale group schemes over an algebraically closed field -/

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Opposite
open scoped CategoryTheory.MonObj

set_option maxHeartbeats 800000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true

noncomputable section

namespace Langlands.GroupScheme

open Langlands.AlgebraicGeometry.FiniteEtale

variable {K : Type u} [Field K] [IsAlgClosed K]

/-- Over an algebraically closed field, a morphism between finite étale schemes is determined
by its effect on rational points. -/
lemma finiteEtale_hom_ext {Y Z : Over (Spec (CommRingCat.of K))}
    [IsFinite Y.hom] [Etale Y.hom] [IsFinite Z.hom] [Etale Z.hom] {f g : Y ⟶ Z}
    (h : ∀ x : Over.mk (𝟙 (Spec (CommRingCat.of K))) ⟶ Y, x ≫ f = x ≫ g) : f = g := by
  obtain ⟨hG, hF⟩ := geometricGaloisFiberFunctor (𝟙 (Spec (CommRingCat.of K)))
    (geometricFiberFinite (𝟙 (Spec (CommRingCat.of K))))
  let := hG
  have := hF
  let Yc : Cover (Spec (CommRingCat.of K)) := ⟨Y, inferInstance, inferInstance⟩
  let Zc : Cover (Spec (CommRingCat.of K)) := ⟨Z, inferInstance, inferInstance⟩
  have hfg : (ObjectProperty.homMk f : Yc ⟶ Zc) = ObjectProperty.homMk g := by
    apply (fiberFunctor (𝟙 (Spec (CommRingCat.of K)))
      (geometricFiberFinite (𝟙 (Spec (CommRingCat.of K))))).map_injective
    ext x
    exact h x
  exact congrArg (fun φ : Yc ⟶ Zc ↦ φ.hom) hfg

/-- A homomorphism to the multiplicative group from a finite étale group scheme killed by an
integer invertible in `K` is trivial as soon as it is trivial on rational points. -/
lemma hom_eq_zero_of_points {H : CommGroupScheme (Spec (CommRingCat.of K))}
    [IsFinite H.X.hom] [Etale H.X.hom] (n : ℕ) (hn : (n : K) ≠ 0)
    (hH : (𝟙 H.X : H.X ⟶ H.X) ^ n = 1) (φ : H ⟶ Gm (Spec (CommRingCat.of K)))
    (hφ : ∀ σ : Over.mk (𝟙 (Spec (CommRingCat.of K))) ⟶ H.X, σ ≫ φ.toMul.hom.hom = 1) :
    φ = 0 := by
  have hn0 : 0 < n := Nat.pos_of_ne_zero (by rintro rfl; exact hn Nat.cast_zero)
  have hunit : IsUnit (n : Γ(Spec (CommRingCat.of K), ⊤)) := by
    have h2 := hn.isUnit.map (Scheme.ΓSpecIso (CommRingCat.of K)).inv.hom
    simpa using h2
  obtain ⟨hfin, het⟩ := muFiniteEtale (Spec (CommRingCat.of K)) n hn0 hunit
  have := hfin
  have := het
  have hψ : φ.toMul.hom.hom ≫
      (multiplication (Gm (Spec (CommRingCat.of K))).toGrp (n : ℤ)).hom.hom = 1 := by
    rw [points_multiplication, zpow_natCast]
    have h := MonObj.pow_comp (𝟙 H.X) n φ.toMul.hom.hom
    rw [Category.id_comp] at h
    rw [← h, hH, MonObj.one_comp]
  let ψ' : H.X ⟶ (mu (Spec (CommRingCat.of K)) n).X :=
    (kernelPointsEquiv (multiplication (Gm (Spec (CommRingCat.of K))).toGrp (n : ℤ))
      H.X).symm ⟨φ.toMul.hom.hom, hψ⟩
  have hψ' : ψ' ≫ (kernelι (multiplication (Gm (Spec (CommRingCat.of K))).toGrp
      (n : ℤ))).hom.hom = φ.toMul.hom.hom :=
    congrArg Subtype.val ((kernelPointsEquiv _ H.X).apply_symm_apply ⟨φ.toMul.hom.hom, hψ⟩)
  have h1 : ψ' = 1 := by
    apply finiteEtale_hom_ext
    intro x
    apply (cancel_mono (kernelι (multiplication (Gm (Spec (CommRingCat.of K))).toGrp
      (n : ℤ))).hom.hom).mp
    simp only [Category.assoc]
    rw [hψ', hφ, MonObj.one_comp, MonObj.comp_one]
  apply Additive.toMul.injective
  apply Grp.hom_ext
  rw [← hψ', h1, MonObj.one_comp]
  rfl

/-- A character of a finite étale group scheme killed by an integer invertible in `K`, over
the identity test scheme, is zero as soon as it evaluates trivially on all rational points. -/
lemma characters_eq_zero_of_evaluation {G : CommGroupScheme (Spec (CommRingCat.of K))}
    [IsFinite G.X.hom] [Etale G.X.hom] (n : ℕ) (hn : (n : K) ≠ 0)
    (hG : multiplication G.toGrp (n : ℤ) = 1)
    (χ : (Cartier.characters G).obj (op (Over.mk (𝟙 (Spec (CommRingCat.of K))))))
    (hχ : ∀ x : Over.mk (𝟙 (Spec (CommRingCat.of K))) ⟶ G.X,
      Cartier.characterEvaluation χ x = 1) : χ = 0 := by
  let T : Over (Spec (CommRingCat.of K)) := Over.mk (𝟙 _)
  let H := Cartier.testBaseChange T G
  have : IsFinite H.X.hom := by
    change IsFinite (pullback.snd G.X.hom T.hom)
    infer_instance
  have : Etale H.X.hom := by
    change Etale (pullback.snd G.X.hom T.hom)
    infer_instance
  have hH : (𝟙 H.X : H.X ⟶ H.X) ^ n = 1 := by
    apply (baseChangePointsEquiv T.hom G.toGrp H.X).injective
    rw [map_pow, map_one, ← zpow_natCast,
      ← points_multiplication G.toGrp (n : ℤ) _ (baseChangePointsEquiv T.hom G.toGrp H.X (𝟙 _)),
      hG]
    exact MonObj.comp_one _
  apply (Cartier.characterHomEquiv G T).injective
  rw [map_zero]
  apply hom_eq_zero_of_points (H := H) n hn hH
  intro σ
  apply (Gm.pointsEquiv T.left (Over.mk (𝟙 T.left))).injective
  rw [map_one]
  obtain ⟨x, rfl⟩ := (Cartier.sectionPointsEquiv G T).symm.surjective σ
  exact (Cartier.characterEvaluation_section χ x).trans (by rw [hχ x, map_one])

end Langlands.GroupScheme
