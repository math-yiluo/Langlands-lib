import Langlands.GroupScheme.HomScheme.AdicSplitTorusFibres

/-! # Extension of algebraized split-torus torsion on valuation tests -/

noncomputable section

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry IsLocalRing

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true
set_option maxHeartbeats 1200000

namespace Langlands.GroupScheme.HomScheme.Adic

open Diagonalizable

variable {A : Type u} [CommRing A] [IsLocalRing A] [IsNoetherianRing A]
  [IsAdicComplete (maximalIdeal A) A] {G : GroupScheme (Spec (CommRingCat.of A))}
variable (L : Type u) [Fintype L]

local notation "S" => Spec (CommRingCat.of A)
local notation "H" => CommGroupScheme.toGrp (groupScheme (CommRingCat.of A) (L → ℤ))

/-- A homomorphism on a test scheme realizes the actual algebraized torsion
restrictions when each of its positive torsion restrictions is their pullback. -/
def System.RealizesSplitTorsion (s : System (maximalIdeal A) H G)
    {V : Over S} (f : RelativeHom H G V) : Prop :=
  ∀ (n : ℕ) (hn : 0 < n), (baseChange V.hom).map
    (splitTorsionRestriction (CommRingCat.of A) L n) ≫ f =
      (baseChange V.hom).map (s.splitTorsionHom L n hn)

namespace System

variable {L}
variable {s : System (maximalIdeal A) (groupScheme (CommRingCat.of A) (L → ℤ)).toGrp G}

/-- Realization of algebraized torsion is preserved by evaluation. -/
theorem RealizesSplitTorsion.evaluate {U V : Over S} {f : RelativeHom H G V}
    (hf : s.RealizesSplitTorsion L f) (a : U ⟶ V) :
    s.RealizesSplitTorsion L (HomScheme.evaluate a f) := by
  intro n hn
  let j := splitTorsionRestriction (CommRingCat.of A) L n
  have hc : HomScheme.evaluate a ((baseChange V.hom).map j ≫ f) =
      HomScheme.evaluate a ((baseChange V.hom).map j) ≫ HomScheme.evaluate a f :=
    Descent.pullHom_comp a.left a.w a.w a.w ((baseChange V.hom).map j) f
  calc
    (baseChange U.hom).map j ≫ HomScheme.evaluate a f =
        HomScheme.evaluate a ((baseChange V.hom).map j ≫ f) := by
          rw [hc, evaluate_baseChange]
    _ = (baseChange U.hom).map (s.splitTorsionHom L n hn) :=
      (congrArg (HomScheme.evaluate a) (hf n hn)).trans (evaluate_baseChange a _)

/-- Positive torsion detects equality of the maps on any test scheme. -/
theorem RealizesSplitTorsion.hom_ext {V : Over S} {f g : RelativeHom H G V}
    (hf : s.RealizesSplitTorsion L f) (hg : s.RealizesSplitTorsion L g) : f = g := by
  let : AddGroup.FG (L → ℤ) := Module.Finite.iff_addGroup_fg.mp inferInstance
  have hH : RelativeMultiplicativeType.IsDiagonalizable H :=
    isDiagonalizable_groupScheme (CommRingCat.of A) (L → ℤ)
  apply hom_eq_of_torsion_restrictions
    (RelativeMultiplicativeType.IsMultiplicativeType.of_isDiagonalizable (hH.baseChange V.hom))
  intro n hn
  let B := baseChange V.hom
  let e := torsionBaseChangeIso V.hom H (n : ℤ)
  let d := torsionIso (CommRingCat.of A) (L → ℤ) n
  apply (cancel_epi e.hom).mp
  rw [← Category.assoc, torsionBaseChangeIso_hom_ι, ← Category.assoc,
    torsionBaseChangeIso_hom_ι]
  apply (cancel_epi (B.map d.inv)).mp
  simp only [← Category.assoc]
  change (B.map d.inv ≫ B.map (torsionι H (n : ℤ))) ≫ f =
    (B.map d.inv ≫ B.map (torsionι H (n : ℤ))) ≫ g
  rw [← Functor.map_comp, torsionIso_inv_comp_ι]
  exact (hf n hn).trans (hg n hn).symm

private theorem unflatten_comp_hom {W U : Scheme.{u}} (b : U ⟶ W) (V : Over U)
    {J K M : GroupScheme W}
    (f : RelativeHom J K ((Over.map b).obj V)) (g : RelativeHom K M ((Over.map b).obj V)) :
    unflatten b V (f ≫ g) = unflatten b V f ≫ unflatten b V g := by
  simp only [unflatten, Category.assoc, Iso.inv_hom_id_assoc]

/-- Over an affine pullback of the target, a torsion realization over
injectively extended coefficients gives a torsion realization over the smaller
ring. -/
theorem exists_realizesSplitTorsion_of_affine {R K : Type u} [CommRing R] [CommRing K]
    (b : Spec (CommRingCat.of R) ⟶ S) [IsAffineHom ((baseChange b).obj G).X.hom]
    (φ : R →+* K) (hφ : Function.Injective φ)
    (f : RelativeHom H G (Over.mk (Spec.map (CommRingCat.ofHom φ) ≫ b)))
    (hf : s.RealizesSplitTorsion L f) :
    ∃ g : RelativeHom H G (Over.mk b), s.RealizesSplitTorsion L g := by
  let j := Spec.map (CommRingCat.ofHom φ)
  let V := Over.mk j
  let B := baseChange b
  let C := baseChange j
  let e := baseChangeIso b (L → ℤ)
  let f₀ := unflatten b V f
  have heval {J K : GroupScheme S} (a : J ⟶ K) :
      unflatten b V ((baseChange ((Over.map b).obj V).hom).map a) = C.map (B.map a) := by
    rw [← evaluate_baseChange (Over.homMk V.hom rfl : (Over.map b).obj V ⟶ Over.mk b) a]
    exact unflatten_flatten b V ((baseChange V.hom).map (B.map a))
  have htor (n : ℕ) (hn : 0 < n) :
      C.map (B.map (splitTorsionRestriction (CommRingCat.of A) L n)) ≫ f₀ =
        C.map (B.map (s.splitTorsionHom L n hn)) := by
    have h : (baseChange ((Over.map b).obj V).hom).map
        (splitTorsionRestriction (CommRingCat.of A) L n) ≫ f =
          (baseChange ((Over.map b).obj V).hom).map (s.splitTorsionHom L n hn) := hf n hn
    simpa only [unflatten_comp_hom, heval] using congrArg (unflatten b V) h
  have htor' (n : ℕ) (hn : 0 < n) :
      ∃ g : (groupScheme (CommRingCat.of R)
          ((L → ℤ) ⧸ TorsionDensity.multiples (L → ℤ) n)).toGrp ⟶ B.obj G,
        C.map g = C.map (splitTorsionRestriction (CommRingCat.of R) L n) ≫ C.map e.inv ≫ f₀ := by
    let d := baseChangeIso b ((L → ℤ) ⧸ TorsionDensity.multiples (L → ℤ) n)
    let a := splitTorsionRestriction (CommRingCat.of A) L n
    let a' := splitTorsionRestriction (CommRingCat.of R) L n
    have hc : d.inv ≫ B.map a = a' ≫ e.inv := by
      apply (cancel_mono e.hom).mp
      rw [Category.assoc, baseChangeIso_restrictMap, Iso.inv_hom_id_assoc,
        Category.assoc, Iso.inv_hom_id, Category.comp_id]
    refine ⟨d.inv ≫ B.map (s.splitTorsionHom L n hn), ?_⟩
    rw [Functor.map_comp, ← htor n hn, ← Functor.map_comp_assoc, hc, Functor.map_comp_assoc]
  obtain ⟨g, hg, _⟩ := existsUnique_baseChange_hom_of_torsion_lifts L φ hφ
    (C.map e.inv ≫ f₀) (0 < ·)
    (fun n => ⟨n + 1, Nat.zero_lt_succ n, Nat.lt_succ_self n⟩) htor'
  let g₀ := e.hom ≫ g
  have hg₀ : C.map g₀ = f₀ := by
    rw [Functor.map_comp, hg, ← Functor.map_comp_assoc, Iso.hom_inv_id, C.map_id,
      Category.id_comp]
  refine ⟨g₀, ?_⟩
  intro n hn
  change B.map (splitTorsionRestriction (CommRingCat.of A) L n) ≫ g₀ =
    B.map (s.splitTorsionHom L n hn)
  let : IsSchemeTheoreticallyDominant j := isSchemeTheoreticallyDominant_specMap hφ
  let : IsSeparated (B.obj G).X.hom := by
    change IsSeparated ((baseChange b).obj G).X.hom
    infer_instance
  let : Flat (B.obj (groupScheme (CommRingCat.of A)
      ((L → ℤ) ⧸ TorsionDensity.multiples (L → ℤ) n)).toGrp).X.hom := by
    change Flat (pullback.snd (groupScheme (CommRingCat.of A)
      ((L → ℤ) ⧸ TorsionDensity.multiples (L → ℤ) n)).X.hom b)
    infer_instance
  apply SchematicHomEquality.baseChange_hom_ext j
  rw [Functor.map_comp, hg₀]
  exact htor n hn

/-- Every discrete valuation ring test admits a homomorphism realizing the
positive torsion restrictions of the given system. -/
def HasSplitTorusHomOnDvrTests (s : System (maximalIdeal A) H G) : Prop :=
  ∀ (R : Type u) [CommRing R] [IsDomain R] [IsDiscreteValuationRing R]
    (b : Spec (CommRingCat.of R) ⟶ S),
    ∃ f : RelativeHom H G (Over.mk b), s.RealizesSplitTorsion L f

/-- For a smooth, separated and quasi-compact target with affine residue fibres,
torsion realizations on the residue fields extend to DVR tests. -/
theorem exists_splitTorusHom_on_dvrTest [Smooth G.X.hom] [IsSeparated G.X.hom]
    [QuasiCompact G.X.hom] (hG : HasAffineResidueFibers G)
    (h : s.HasSplitTorusHomOnResidueFields L) : s.HasSplitTorusHomOnDvrTests := by
  intro R _ _ _ b
  let K := FractionRing R
  let j := Spec.map (CommRingCat.ofHom (algebraMap R K))
  let y := (j ≫ b) (closedPoint K)
  let q := Scheme.fromSpecResidueField S y
  let c := Spec.map (Scheme.descResidueField (Scheme.stalkClosedPointTo (j ≫ b)))
  have hc : c ≫ q = j ≫ b :=
    Scheme.descResidueField_stalkClosedPointTo_fromSpecResidueField K S (j ≫ b)
  let a : Over.mk (j ≫ b) ⟶ Over.mk q := Over.homMk c hc
  obtain ⟨f, hf⟩ := h y
  let : IsAffineHom ((baseChange b).obj G).X.hom :=
    G.isAffineHom_dvrPullback_of_residueFibers hG b
  exact exists_realizesSplitTorsion_of_affine b (algebraMap R K)
    (IsFractionRing.injective R K) (HomScheme.evaluate a f)
    ((show s.RealizesSplitTorsion L f from hf).evaluate a)

end System

end Langlands.GroupScheme.HomScheme.Adic
