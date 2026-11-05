import Langlands.Geometry.Building.CentralIsogenyTranslation
import Langlands.GroupScheme.Rational.DerivedRelativeRoots
import Langlands.GroupScheme.Rational.SplitTorusSurjection
import Langlands.GroupScheme.Torus.MaximalAmbient

/-! # Reduced translation spaces through an actual derived inclusion -/

noncomputable section

set_option backward.isDefEq.respectTransparency false

universe u

open CategoryTheory AlgebraicGeometry TensorProduct
open CategoryTheory.MonoidalCategory CategoryTheory.CartesianMonoidalCategory
open scoped CategoryTheory.MonObj
open Langlands.GroupScheme Langlands.GroupScheme.RealTorusSpace

namespace Langlands.Geometry.Building

variable {k : Type u} [Field k]
    {T A S : CommGroupScheme (Spec (CommRingCat.of k))}

private abbrev productTorus (T A : CommGroupScheme (Spec (CommRingCat.of k)))
    (hT : IsSplitTorus T.toGrp) (hA : IsSplitTorus A.toGrp) :
    CommGroupScheme (Spec (CommRingCat.of k)) where
  toGrp := T.toGrp ⊗ A.toGrp
  comm := (hT.tensor hA).isCommMonObj

section Product

variable (e : T ⟶ S) (c : A ⟶ S)
    (hT : IsSplitTorus T.toGrp) (hA : IsSplitTorus A.toGrp)
    (hS : IsSplitTorus S.toGrp)
    [hpflat : Flat (RelativeRoot.centralComplementProduct e c).hom.hom.left]
    [hpsurj : Surjective (RelativeRoot.centralComplementProduct e c).hom.hom.left]

include hpflat hpsurj hT hA hS in
/-- A flat-surjective product of split tori decomposes every real cocharacter
as the sum of the two actual factor images. -/
theorem exists_eq_cocharacterMapReal_add_of_centralComplement (v : V S) :
    ∃ (w : V T) (z : V A),
      v = cocharacterMapReal e w + cocharacterMapReal c z := by
  let P := productTorus T A hT hA
  let p : P ⟶ S := Additive.ofMul (RelativeRoot.centralComplementProduct e c)
  let pr₁ : P ⟶ T := Additive.ofMul (fst T.toGrp A.toGrp)
  let pr₂ : P ⟶ A := Additive.ofMul (snd T.toGrp A.toGrp)
  have hp : IsSplitTorus P.toGrp := hT.tensor hA
  have : Flat (CommGroupScheme.groupHom p).hom.hom.left := hpflat
  have : Surjective (CommGroupScheme.groupHom p).hom.hom.left := hpsurj
  have : Epi (CommGroupScheme.groupHom p).hom.hom.left :=
    Flat.epi_of_flat_of_surjective _
  obtain ⟨u, rfl⟩ := cocharacterMapReal_surjective_of_epi hp hS p v
  refine ⟨cocharacterMapReal pr₁ u, cocharacterMapReal pr₂ u, ?_⟩
  induction u using TensorProduct.inductionOn with
  | tmul r ν =>
    simp only [cocharacterMapReal_tmul]
    rw [← TensorProduct.tmul_add]
    congr 1
    apply Additive.toMul.injective
    apply GroupScheme.hom_ext_points
    intro U x
    change x ≫ (ν.toMul ≫ RelativeRoot.centralComplementProduct e c).hom.hom =
      x ≫ (((ν.toMul ≫ fst T.toGrp A.toGrp) ≫ e.toMul) *
        ((ν.toMul ≫ snd T.toGrp A.toGrp) ≫ c.toMul)).hom.hom
    simp only [Grp.Hom.hom_mul, Mon.Hom.hom_mul, MonObj.comp_mul, Grp.comp_hom_hom]
    simpa only [Category.assoc, productPointsEquiv_fst, productPointsEquiv_snd,
      Grp.fst_hom_hom, Grp.snd_hom_hom] using
      comp_prodHom (CommGroupScheme.groupHom e) (CommGroupScheme.groupHom c)
        (fun _ _ _ => Commute.all _ _) U (x ≫ ν.toMul.hom.hom)
  | add u v hu hv => simp only [map_add, hu, hv]; abel

end Product

variable {D G : GroupScheme (Spec (CommRingCat.of k))}
    [IsAffineHom D.X.hom] [LocallyOfFiniteType D.X.hom]
    [IsAffineHom G.X.hom] [Smooth G.X.hom]
    (e : T ⟶ S) (c : A ⟶ S) (j : T.toGrp ⟶ D) (i : S.toGrp ⟶ G)
    (d : D ⟶ G) (hd : IsDerivedSubgroup d)
    (h : j ≫ d = CommGroupScheme.groupHom e ≫ i)
    (hT : IsSplitTorus T.toGrp) (hS : IsSplitTorus S.toGrp)
    (hA : IsSplitTorus A.toGrp)
    [hpflat : Flat (RelativeRoot.centralComplementProduct e c).hom.hom.left]
    [hpsurj : Surjective (RelativeRoot.centralComplementProduct e c).hom.hom.left]
    (hc : IsCentral (CommGroupScheme.groupHom c ≫ i))

include hpflat hpsurj hd h hT hS hA hc in
/-- The actual retained-torus cocharacter map preserves and reflects the
common root kernel. -/
theorem cocharacterMapReal_mem_rootAnnihilator_derived_iff (v : V T) :
    cocharacterMapReal e v ∈ rootAnnihilator i ↔ v ∈ rootAnnihilator j := by
  rw [mem_rootAnnihilator, mem_rootAnnihilator]
  constructor
  · intro hv b hb
    obtain ⟨a, ha, hab⟩ :=
      RelativeRoot.exists_relativeRoot_precomp_eq_derived e j i d hd h hT hS hb
    rw [← hab, ← eval_cocharacterMapReal]
    exact hv a ha
  · intro hv a ha
    rw [eval_cocharacterMapReal]
    exact hv (e ≫ a)
      (RelativeRoot.mem_relativeRoots_precomp_derived e c j i d hd h hT hS hA hc ha)

/-- The quotient map induced by the literal retained-torus morphism. -/
def derivedTranslationMap : TranslationSpace j →ₗ[ℝ] TranslationSpace i :=
  (rootAnnihilator j).liftQ
    ((rootAnnihilator i).mkQ.comp (cocharacterMapReal e)) fun v hv => by
      change (Submodule.Quotient.mk (cocharacterMapReal e v) : TranslationSpace i) = 0
      exact (Submodule.Quotient.mk_eq_zero _).mpr
        ((cocharacterMapReal_mem_rootAnnihilator_derived_iff
          e c j i d hd h hT hS hA hc v).mpr hv)

@[simp]
theorem derivedTranslationMap_mk (v : V T) :
    derivedTranslationMap e c j i d hd h hT hS hA hc (Submodule.Quotient.mk v) =
      Submodule.Quotient.mk (cocharacterMapReal e v) := rfl

theorem derivedTranslationMap_injective :
    Function.Injective (derivedTranslationMap e c j i d hd h hT hS hA hc) := by
  apply LinearMap.ker_eq_bot.mp
  apply le_antisymm ?_ bot_le
  intro u hu
  change u = 0
  rw [LinearMap.mem_ker] at hu
  induction u using Submodule.Quotient.induction_on with
  | _ v =>
    change (Submodule.Quotient.mk (cocharacterMapReal e v) : TranslationSpace i) = 0 at hu
    apply (Submodule.Quotient.mk_eq_zero _).mpr
    exact (cocharacterMapReal_mem_rootAnnihilator_derived_iff
      e c j i d hd h hT hS hA hc v).mp ((Submodule.Quotient.mk_eq_zero _).mp hu)

theorem derivedTranslationMap_surjective :
    Function.Surjective (derivedTranslationMap e c j i d hd h hT hS hA hc) := by
  intro u
  induction u using Submodule.Quotient.induction_on with
  | _ v =>
    obtain ⟨w, z, hv⟩ :=
      exists_eq_cocharacterMapReal_add_of_centralComplement e c hT hA hS v
    refine ⟨Submodule.Quotient.mk w, ?_⟩
    change (Submodule.Quotient.mk (cocharacterMapReal e w) : TranslationSpace i) =
      Submodule.Quotient.mk v
    rw [Submodule.Quotient.eq]
    have hz : cocharacterMapReal c z ∈ rootAnnihilator i := by
      rw [mem_rootAnnihilator]
      intro a ha
      rw [eval_cocharacterMapReal, root_restrict_eq_zero_of_isCentral i c hA hc ha,
        eval_zero_char]
    have hv' : cocharacterMapReal e w - v = -cocharacterMapReal c z := by
      rw [hv]
      abel
    rw [hv']
    exact (rootAnnihilator i).neg_mem hz

/-- The original reduced cocharacter spaces are linearly equivalent through
the literal derived-torus morphism; it need not be an isogeny of tori. -/
def derivedTranslationEquiv : TranslationSpace j ≃ₗ[ℝ] TranslationSpace i :=
  LinearEquiv.ofBijective
    (derivedTranslationMap e c j i d hd h hT hS hA hc)
    ⟨derivedTranslationMap_injective e c j i d hd h hT hS hA hc,
      derivedTranslationMap_surjective e c j i d hd h hT hS hA hc⟩

@[simp]
theorem derivedTranslationEquiv_mk (v : V T) :
    derivedTranslationEquiv e c j i d hd h hT hS hA hc (Submodule.Quotient.mk v) =
      Submodule.Quotient.mk (cocharacterMapReal e v) := rfl

theorem rootForm_derivedTranslationEquiv (a : relativeRoots i) (v : TranslationSpace j) :
    rootForm i a (derivedTranslationEquiv e c j i d hd h hT hS hA hc v) =
      rootForm j (RelativeRoot.derivedRelativeRootEquiv e c j i d hd h hT hS hA hc a) v := by
  refine Submodule.Quotient.induction_on _ v fun w => ?_
  exact eval_cocharacterMapReal e a.val w

end Langlands.Geometry.Building
