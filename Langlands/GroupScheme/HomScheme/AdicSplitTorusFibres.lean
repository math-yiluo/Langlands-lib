import Langlands.AlgebraicGeometry.Modules.IdealAdicClosedFibre
import Langlands.AlgebraicGeometry.ProperOfFibres.ValuationCore
import Langlands.GroupScheme.HomScheme.AdicDvrSpecialization
import Langlands.GroupScheme.HomScheme.AdicTorsionBaseChange
import Langlands.GroupScheme.Torus.AffineRelativeDiagonalizable

/-! # Fibre homomorphisms of a formal split-torus homomorphism -/

noncomputable section

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry IsLocalRing
open Langlands.AlgebraicGeometry.AdicAffinePoints

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true
set_option maxHeartbeats 1200000

namespace Langlands.GroupScheme.HomScheme.Adic

open Diagonalizable

private theorem evaluate_comp_hom {S : Scheme.{u}} {T T' : Over S}
    {J H G : GroupScheme S} (a : T' ⟶ T) (f : RelativeHom J H T) (g : RelativeHom H G T) :
    evaluate a (f ≫ g) = evaluate a f ≫ evaluate a g :=
  Descent.pullHom_comp a.left a.w a.w a.w f g

private theorem unflatten_comp_hom {S U : Scheme.{u}} (q : U ⟶ S) (V : Over U)
    {J H G : GroupScheme S}
    (f : RelativeHom J H ((Over.map q).obj V)) (g : RelativeHom H G ((Over.map q).obj V)) :
    unflatten q V (f ≫ g) = unflatten q V f ≫ unflatten q V g := by
  simp only [unflatten, Category.assoc, Iso.inv_hom_id_assoc]

private theorem unflatten_evaluate_constant {S U : Scheme.{u}} (q : U ⟶ S) (V : Over U)
    {H G : GroupScheme S} (f : RelativeHom H G (Over.mk q)) :
    unflatten q V (evaluate (Over.homMk V.hom rfl : (Over.map q).obj V ⟶ Over.mk q) f) =
      (baseChange V.hom).map f := by
  rw [← flatten_baseChange, unflatten_flatten]

variable {R A B : Type u} [CommRing R] [CommRing A] [CommRing B]

private theorem exists_relativeHom_of_torsion_lifts (L : Type u) [Fintype L]
    {G : GroupScheme (Spec (CommRingCat.of R))} (q : Spec (CommRingCat.of A) ⟶ Spec (CommRingCat.of R))
    [IsAffineHom ((baseChange q).obj G).X.hom]
    (φ : A →+* B) (hφ : Function.Injective φ) :
    let V := Over.mk (Spec.map (CommRingCat.ofHom φ))
    let a : (Over.map q).obj V ⟶ Over.mk q := Over.homMk V.hom rfl
    ∀ f : RelativeHom (groupScheme (CommRingCat.of R) (L → ℤ)).toGrp G ((Over.map q).obj V),
    (∀ n : ℕ, 0 < n →
      ∃ g : RelativeHom (groupScheme (CommRingCat.of R)
          ((L → ℤ) ⧸ TorsionDensity.multiples (L → ℤ) n)).toGrp G (Over.mk q),
        evaluate a g = (baseChange ((Over.map q).obj V).hom).map
            (splitTorsionRestriction (CommRingCat.of R) L n) ≫ f) →
    ∃ g : RelativeHom (groupScheme (CommRingCat.of R) (L → ℤ)).toGrp G (Over.mk q),
      evaluate a g = f := by
  intro V a f ht
  let C := baseChange (Spec.map (CommRingCat.ofHom φ))
  let e := baseChangeIso q (L → ℤ)
  have heval {J K : GroupScheme (Spec (CommRingCat.of R))}
      (g : RelativeHom J K (Over.mk q)) :
      unflatten q V (evaluate a g) = C.map g :=
    unflatten_evaluate_constant q V g
  let f' := C.map e.inv ≫ unflatten q V f
  have htor (n : ℕ) (hn : 0 < n) :
      ∃ g : (groupScheme (CommRingCat.of A)
          ((L → ℤ) ⧸ TorsionDensity.multiples (L → ℤ) n)).toGrp ⟶ (baseChange q).obj G,
        C.map g = C.map (splitTorsionRestriction (CommRingCat.of A) L n) ≫ f' := by
    obtain ⟨g, hg⟩ := ht n hn
    let d := baseChangeIso q ((L → ℤ) ⧸ TorsionDensity.multiples (L → ℤ) n)
    let j := splitTorsionRestriction (CommRingCat.of R) L n
    let j' := splitTorsionRestriction (CommRingCat.of A) L n
    have hcomp : d.inv ≫ (baseChange q).map j = j' ≫ e.inv := by
      apply (cancel_mono e.hom).mp
      rw [Category.assoc, baseChangeIso_restrictMap, Iso.inv_hom_id_assoc,
        Category.assoc, Iso.inv_hom_id, Category.comp_id]
    have hj : unflatten q V ((baseChange ((Over.map q).obj V).hom).map j) =
        C.map ((baseChange q).map j) :=
      (congrArg (unflatten q V) (evaluate_baseChange a j).symm).trans (heval _)
    have h := congrArg (unflatten q V) hg
    rw [heval, unflatten_comp_hom] at h
    have h' := h.trans (congrArg (· ≫ unflatten q V f) hj)
    refine ⟨d.inv ≫ g, ?_⟩
    change C.map (d.inv ≫ g) = C.map j' ≫ C.map e.inv ≫ unflatten q V f
    rw [Functor.map_comp, h', ← Functor.map_comp_assoc, hcomp, Functor.map_comp_assoc]
  obtain ⟨g, hg, _⟩ := existsUnique_baseChange_hom_of_torsion_lifts L φ hφ f' (0 < ·)
    (fun n => ⟨n + 1, Nat.zero_lt_succ n, Nat.lt_succ_self n⟩) htor
  refine ⟨e.hom ≫ g, (flattenEquiv q V).symm.injective ?_⟩
  change unflatten q V (evaluate a (e.hom ≫ g)) = unflatten q V f
  rw [heval]
  change C.map (e.hom ≫ g) = unflatten q V f
  rw [Functor.map_comp, hg]
  dsimp only [f']
  rw [← Functor.map_comp_assoc, Iso.hom_inv_id, C.map_id, Category.id_comp]

variable [IsLocalRing R] [IsNoetherianRing R] [IsAdicComplete (maximalIdeal R) R]
variable {G : GroupScheme (Spec (CommRingCat.of R))}

private def closedPointToFirstQuotient :
    Over.mk ((Spec (CommRingCat.of R)).fromSpecResidueField (closedPoint R)) ⟶
      Over.mk (quotientMap (maximalIdeal R) 0) := by
  let e := (Ideal.quotEquivOfEq (pow_one (maximalIdeal R))).toCommRingCatIso
  let d := AlgebraicGeometry.Modules.IdealAdic.residueFieldClosedPointIso (CommRingCat.of R)
  refine Over.homMk (Spec.map (e.hom ≫ d.hom)) ?_
  rw [Spec.map_comp, Category.assoc, AlgebraicGeometry.Modules.IdealAdic.fromSpecResidueField_closedPoint]
  congr 1
  change Spec.map e.hom ≫ Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk (maximalIdeal R ^ 1))) = _
  rw [← Spec.map_comp]
  congr 1

private theorem exists_splitTorusHom_on_closedPoint (L : Type u) [Fintype L]
    (s : System (maximalIdeal R) (groupScheme (CommRingCat.of R) (L → ℤ)).toGrp G) :
    ∃ f : RelativeHom (groupScheme (CommRingCat.of R) (L → ℤ)).toGrp G
      (Over.mk ((Spec (CommRingCat.of R)).fromSpecResidueField (closedPoint R))),
      ∀ (n : ℕ) (hn : 0 < n),
        (baseChange ((Spec (CommRingCat.of R)).fromSpecResidueField (closedPoint R))).map
          (splitTorsionRestriction (CommRingCat.of R) L n) ≫ f =
        (baseChange ((Spec (CommRingCat.of R)).fromSpecResidueField (closedPoint R))).map
          (s.splitTorsionHom L n hn) := by
  let d := closedPointToFirstQuotient (R := R)
  refine ⟨evaluate d (s.hom 0), ?_⟩
  intro n hn
  have h := congrArg (evaluate d) (s.splitTorsionHom_reduce L n hn 0)
  rw [evaluate_comp_hom] at h
  exact (congrArg (· ≫ evaluate d (s.hom 0))
    (evaluate_baseChange d (splitTorsionRestriction (CommRingCat.of R) L n)).symm).trans
      (h.symm.trans (evaluate_baseChange d (s.splitTorsionHom L n hn)))

/-- Every residue field of the complete local base has a split-torus
homomorphism realizing the algebraized positive torsion restrictions. -/
def System.HasSplitTorusHomOnResidueFields
    (L : Type u) [Fintype L]
    (s : System (maximalIdeal R) (groupScheme (CommRingCat.of R) (L → ℤ)).toGrp G) : Prop :=
  ∀ y : Spec (CommRingCat.of R),
    ∃ f : RelativeHom (groupScheme (CommRingCat.of R) (L → ℤ)).toGrp G
      (Over.mk ((Spec (CommRingCat.of R)).fromSpecResidueField y)),
      ∀ (n : ℕ) (hn : 0 < n),
        (baseChange ((Spec (CommRingCat.of R)).fromSpecResidueField y)).map
          (splitTorsionRestriction (CommRingCat.of R) L n) ≫ f =
        (baseChange ((Spec (CommRingCat.of R)).fromSpecResidueField y)).map
          (s.splitTorsionHom L n hn)

/-- The closed-point map is the first quotient map, and at each other point
a completed DVR lift descends along the residue-field extension. -/
theorem System.exists_splitTorusHom_on_residueField
    [Smooth G.X.hom] [IsSeparated G.X.hom] [QuasiCompact G.X.hom] (hG : HasAffineResidueFibers G)
    (L : Type u) [Fintype L]
    (s : System (maximalIdeal R) (groupScheme (CommRingCat.of R) (L → ℤ)).toGrp G) :
    s.HasSplitTorusHomOnResidueFields L := by
  intro y
  by_cases hy : y = closedPoint R
  · subst y
    exact exists_splitTorusHom_on_closedPoint L s
  let H := (groupScheme (CommRingCat.of R) (L → ℤ)).toGrp
  let : AddGroup.FG (L → ℤ) := Module.Finite.iff_addGroup_fg.mp inferInstance
  have hH : RelativeMultiplicativeType.IsDiagonalizable H :=
    isDiagonalizable_groupScheme (CommRingCat.of R) (L → ℤ)
  obtain ⟨B, ψ, hcomplete, x, hx, f, hf⟩ := completedDvrSpecializationEffectivity R H G hH hG s y hy
  subst y
  let b := Spec.map (CommRingCat.ofHom ψ)
  let q := (Spec (CommRingCat.of R)).fromSpecResidueField (b x)
  let φ := (b.residueFieldMap x).hom
  let c := Spec.map (CommRingCat.ofHom φ)
  let V := Over.mk c
  let a : (Over.map q).obj V ⟶ Over.mk q := Over.homMk c rfl
  let d : (Over.map q).obj V ⟶ Over.mk b := Over.homMk ((Spec B).fromSpecResidueField x)
    (b.SpecMap_residueFieldMap_fromSpecResidueField x).symm
  let f' := evaluate d f
  let : IsAffineHom ((baseChange q).obj G).X.hom := hG (b x)
  let : IsAdicComplete ((maximalIdeal R).map ψ) B := hcomplete
  have htor (n : ℕ) (hn : 0 < n) :
      evaluate a ((baseChange q).map (s.splitTorsionHom L n hn)) =
        (baseChange ((Over.map q).obj V).hom).map
          (splitTorsionRestriction (CommRingCat.of R) L n) ≫ f' := by
    have h := congrArg (evaluate d) (s.baseChange_splitTorsionHom L ψ f hf n hn)
    rw [evaluate_comp_hom] at h
    exact (evaluate_baseChange a (s.splitTorsionHom L n hn)).trans
      ((evaluate_baseChange d (s.splitTorsionHom L n hn)).symm.trans (h.trans
        (congrArg (· ≫ f') (evaluate_baseChange d (splitTorsionRestriction (CommRingCat.of R) L n)))))
  obtain ⟨g, hg⟩ := exists_relativeHom_of_torsion_lifts L q φ φ.injective f'
    (fun n hn => ⟨_, htor n hn⟩)
  refine ⟨g, ?_⟩
  intro n hn
  have hc := Langlands.AlgebraicGeometry.ProperOfFibres.surjective_flat_quasiCompact_SpecMap φ
  let : Flat a.left := hc.1.2
  let : Surjective a.left := hc.1.1
  let : QuasiCompact a.left := hc.2
  apply evaluate_injective_of_flat_surjective a
  exact (evaluate_comp_hom a _ _).trans
    ((congrArg₂ (· ≫ ·) (evaluate_baseChange a
      (splitTorsionRestriction (CommRingCat.of R) L n)) hg).trans (htor n hn).symm)

end Langlands.GroupScheme.HomScheme.Adic
