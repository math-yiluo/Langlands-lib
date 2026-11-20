import Langlands.AlgebraicGeometry.AdicQuotientBaseChange
import Langlands.AlgebraicGeometry.AdicFiniteSource
import Langlands.GroupScheme.HomScheme.AdicSystem
import Langlands.GroupScheme.HomScheme.FibreComparison

/-! # Adic Hom comparison for a finite group source -/

noncomputable section

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry IsLocalRing
open CategoryTheory.MonoidalCategory CategoryTheory.CartesianMonoidalCategory
open scoped CategoryTheory.MonObj
open Langlands.AlgebraicGeometry.AdicAffinePoints

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true

namespace Langlands.GroupScheme.HomScheme.Adic

variable {A : Type u} [CommRing A]

/-- The first projection from a base change to an adic quotient. -/
abbrev finiteSourceReduction (I : Ideal A) {Y : Scheme.{u}}
    (p : Y ⟶ Spec (CommRingCat.of A)) (n : ℕ) : pullback p (quotientMap I n) ⟶ Y :=
  pullback.fst p (quotientMap I n)

/-- The canonical transition between the adic thickenings of a scheme. -/
def finiteSourceTransition (I : Ideal A) {Y : Scheme.{u}}
    (p : Y ⟶ Spec (CommRingCat.of A)) (n : ℕ) :
    pullback p (quotientMap I n) ⟶ pullback p (quotientMap I (n + 1)) :=
  pullback.lift (finiteSourceReduction I p n) (pullback.snd p (quotientMap I n) ≫ transition I n)
    (by rw [Category.assoc, transition_quotientMap, pullback.condition])

@[reassoc (attr := simp)] theorem finiteSourceTransition_fst (I : Ideal A)
    {Y : Scheme.{u}} (p : Y ⟶ Spec (CommRingCat.of A)) (n : ℕ) :
    finiteSourceTransition I p n ≫ finiteSourceReduction I p (n + 1) =
      finiteSourceReduction I p n := pullback.lift_fst _ _ _

@[reassoc (attr := simp)] theorem finiteSourceTransition_snd (I : Ideal A)
    {Y : Scheme.{u}} (p : Y ⟶ Spec (CommRingCat.of A)) (n : ℕ) :
    finiteSourceTransition I p n ≫ pullback.snd p (quotientMap I (n + 1)) =
      pullback.snd p (quotientMap I n) ≫ transition I n := pullback.lift_snd _ _ _

section Coordinates

open Langlands.AlgebraicGeometry (isPushout_quotient_map)

variable (I : Ideal A) {B : Type u} [CommRing B] (φ : A →+* B)

variable {Y : Scheme.{u}} (p : Y ⟶ Spec (CommRingCat.of A))
  (e : Spec (CommRingCat.of B) ≅ Y) (he : e.hom ≫ p = Spec.map (CommRingCat.ofHom φ))

include he

private theorem sourceLevel_isPullback (n : ℕ) :
    IsPullback (quotientMap (I.map φ) n ≫ e.hom) (quotientSpecMap φ I n)
      p (quotientMap I n) :=
  (isPullback_quotientSpecMap φ I n).flip.of_iso (Iso.refl _) e (Iso.refl _) (Iso.refl _)
    (by simp) (by simp) (by simpa using he.symm) (by simp)

private def sourceLevelIso (n : ℕ) : quotientSpec (I.map φ) n ≅ pullback p (quotientMap I n) :=
  (sourceLevel_isPullback I φ p e he n).isoPullback

@[reassoc] private theorem sourceLevelIso_fst (n : ℕ) :
    (sourceLevelIso I φ p e he n).hom ≫ finiteSourceReduction I p n =
      quotientMap (I.map φ) n ≫ e.hom :=
  IsPullback.isoPullback_hom_fst (sourceLevel_isPullback I φ p e he n)

@[reassoc] private theorem sourceLevelIso_snd (n : ℕ) :
    (sourceLevelIso I φ p e he n).hom ≫ pullback.snd p (quotientMap I n) =
      quotientSpecMap φ I n :=
  IsPullback.isoPullback_hom_snd (sourceLevel_isPullback I φ p e he n)

private theorem sourceLevelIso_transition (n : ℕ) :
    transition (I.map φ) n ≫ (sourceLevelIso I φ p e he (n + 1)).hom =
      (sourceLevelIso I φ p e he n).hom ≫ finiteSourceTransition I p n := by
  apply pullback.hom_ext
  · change (transition (I.map φ) n ≫ (sourceLevelIso I φ p e he (n + 1)).hom) ≫
      finiteSourceReduction I p (n + 1) =
        ((sourceLevelIso I φ p e he n).hom ≫ finiteSourceTransition I p n) ≫
          finiteSourceReduction I p (n + 1)
    simp only [Category.assoc, sourceLevelIso_fst, finiteSourceTransition_fst]
    rw [← Category.assoc, transition_quotientMap]
  · simp only [Category.assoc, sourceLevelIso_snd, finiteSourceTransition_snd,
      sourceLevelIso_snd_assoc, quotientSpecMap_transition]

end Coordinates

variable [IsLocalRing A] [IsNoetherianRing A] [IsAdicComplete (maximalIdeal A) A]

set_option maxHeartbeats 700000 in
/-- Compatible maps from the actual base changes of a finite scheme over a
complete noetherian local ring identify with actual maps from that scheme. -/
theorem existsUnique_adic_lift_of_isFinite {Y X : Scheme.{u}}
    (p : Y ⟶ Spec (CommRingCat.of A)) [IsFinite p]
    (f : ∀ n : ℕ, pullback p (quotientMap (maximalIdeal A) n) ⟶ X)
    (hf : ∀ n : ℕ, finiteSourceTransition (maximalIdeal A) p n ≫ f (n + 1) = f n) :
    ∃! g : Y ⟶ X, ∀ n : ℕ, finiteSourceReduction (maximalIdeal A) p n ≫ g = f n := by
  have : IsAffine Y := isAffine_of_isAffineHom p
  let e := Y.isoSpec.symm
  let B := Γ(Y, ⊤)
  let φ : A →+* B := (Spec.preimage (e.hom ≫ p)).hom
  let : Algebra A B := φ.toAlgebra
  have hφ : e.hom ≫ p = Spec.map (CommRingCat.ofHom φ) := (Spec.map_preimage _).symm
  have : IsFinite (Spec.map (CommRingCat.ofHom φ)) := hφ ▸ (inferInstance : IsFinite (e.hom ≫ p))
  have : Module.Finite A B := RingHom.finite_algebraMap.mp ((IsFinite.SpecMap_iff _).mp inferInstance)
  let I := maximalIdeal A
  let l := sourceLevelIso I φ p e hφ
  let v (n : ℕ) := (l n).hom ≫ f n
  have hv (n : ℕ) : transition (I.map φ) n ≫ v (n + 1) = v n := by
    change transition (I.map φ) n ≫ (l (n + 1)).hom ≫ f (n + 1) = (l n).hom ≫ f n
    rw [← Category.assoc, sourceLevelIso_transition I φ p e hφ n, Category.assoc, hf n]
  obtain ⟨g, hg, hgu⟩ := Langlands.AlgebraicGeometry.AdicFiniteSource.adicFiniteAlgebraSource A B X v hv
  change ∀ n : ℕ, quotientMap (I.map φ) n ≫ g = v n at hg
  refine ⟨e.inv ≫ g, fun n => ?_, fun g' hg' => ?_⟩
  · apply (cancel_epi ((l n).hom)).mp
    rw [← Category.assoc, sourceLevelIso_fst I φ p e hφ n, Category.assoc,
      e.hom_inv_id_assoc, hg n]
  · have h : e.hom ≫ g' = g := hgu _ fun n => by
      change quotientMap (I.map φ) n ≫ e.hom ≫ g' = v n
      rw [← Category.assoc, ← sourceLevelIso_fst I φ p e hφ n, Category.assoc, hg' n]
    rw [← h, e.inv_hom_id_assoc]

/-- Maps from a finite scheme over a complete local base are determined by
their restrictions to the adic thickenings. -/
theorem adic_ext_of_isFiniteSource {Y X : Scheme.{u}}
    (p : Y ⟶ Spec (CommRingCat.of A)) [IsFinite p] {f g : Y ⟶ X}
    (h : ∀ n : ℕ, finiteSourceReduction (maximalIdeal A) p n ≫ f =
      finiteSourceReduction (maximalIdeal A) p n ≫ g) : f = g := by
  obtain ⟨q, _, hq⟩ := existsUnique_adic_lift_of_isFinite p
    (fun n => finiteSourceReduction (maximalIdeal A) p n ≫ f)
    (fun n => finiteSourceTransition_fst_assoc _ _ _ _)
  exact (hq f fun _ => rfl).trans (hq g fun n => (h n).symm).symm

omit [IsNoetherianRing A] [IsAdicComplete (maximalIdeal A) A] in
private theorem overMap_fst {Y X : Over (Spec (CommRingCat.of A))} (f : Y ⟶ X)
    (n : ℕ) :
    ((Over.pullback (quotientMap (maximalIdeal A) n)).map f).left ≫
      finiteSourceReduction (maximalIdeal A) X.hom n =
        finiteSourceReduction (maximalIdeal A) Y.hom n ≫ f.left :=
  pullback.lift_fst _ _ _

private theorem over_adic_ext_of_isFiniteSource {Y X : Over (Spec (CommRingCat.of A))}
    [IsFinite Y.hom] {f g : Y ⟶ X}
    (h : ∀ n : ℕ, (Over.pullback (quotientMap (maximalIdeal A) n)).map f =
      (Over.pullback (quotientMap (maximalIdeal A) n)).map g) : f = g := by
  apply Over.OverMorphism.ext
  apply adic_ext_of_isFiniteSource Y.hom
  intro n
  rw [← overMap_fst f n, ← overMap_fst g n, h n]

variable {H G : GroupScheme (Spec (CommRingCat.of A))}

private abbrev systemSchemeMap (s : System (maximalIdeal A) H G) (n : ℕ) :
    pullback H.X.hom (quotientMap (maximalIdeal A) n) ⟶ G.X.left :=
  (s.hom n).hom.hom.left ≫ finiteSourceReduction (maximalIdeal A) G.X.hom n

omit [IsNoetherianRing A] [IsAdicComplete (maximalIdeal A) A] in
set_option maxHeartbeats 900000 in
private theorem systemSchemeMap_compatible (s : System (maximalIdeal A) H G) (n : ℕ) :
    finiteSourceTransition (maximalIdeal A) H.X.hom n ≫ systemSchemeMap s (n + 1) =
      systemSchemeMap s n := by
  let I := maximalIdeal A
  let p := quotientMap I (n + 1)
  let r := quotientMap I n
  let q := transition I n
  let eH := Descent.pullbackComparison p q r (transition_quotientMap I n) H
  let eG := Descent.pullbackComparison p q r (transition_quotientMap I n) G
  let k := (s.hom (n + 1)).hom.hom
  have hproj : eH.inv.hom.hom.left ≫ pullback.fst ((baseChange p).obj H).X.hom q =
      finiteSourceTransition I H.X.hom n := by
    apply pullback.hom_ext
    · rw [Category.assoc, finiteSourceTransition_fst]
      exact Descent.pullbackComparison_inv_fst p q r _ H
    · have hcond : pullback.fst ((baseChange p).obj H).X.hom q ≫ pullback.snd H.X.hom p =
          pullback.snd ((baseChange p).obj H).X.hom q ≫ q := pullback.condition
      have hw : eH.inv.hom.hom.left ≫ pullback.snd ((baseChange p).obj H).X.hom q =
          pullback.snd H.X.hom r := eH.inv.hom.hom.w
      rw [Category.assoc, hcond, ← Category.assoc, hw]
      exact (finiteSourceTransition_snd I H.X.hom n).symm
  have hh : eH.inv ≫ (baseChange q).map (s.hom (n + 1)) ≫ eG.hom = s.hom n :=
    s.compatible n
  have h₁ := congrArg (fun a => a.hom.hom.left ≫ finiteSourceReduction I G.X.hom n) hh
  change _ = systemSchemeMap s n at h₁
  simp only [Grp.comp_hom_hom, Over.comp_left, Category.assoc] at h₁
  have h₂ : eG.hom.hom.hom.left ≫ finiteSourceReduction I G.X.hom n =
      pullback.fst ((baseChange p).obj G).X.hom q ≫ finiteSourceReduction I G.X.hom (n + 1) :=
    Descent.pullbackComparison_hom_fst p q r _ G
  have h₃ : ((Over.pullback q).map k).left ≫ pullback.fst ((baseChange p).obj G).X.hom q =
      pullback.fst ((baseChange p).obj H).X.hom q ≫ k.left :=
    pullback.lift_fst _ _ _
  change eH.inv.hom.hom.left ≫ ((Over.pullback q).map k).left ≫
    eG.hom.hom.hom.left ≫ finiteSourceReduction I G.X.hom n = _ at h₁
  rw [h₂, ← Category.assoc ((Over.pullback q).map k).left, h₃,
    Category.assoc, ← Category.assoc eH.inv.hom.hom.left, hproj] at h₁
  exact h₁

set_option maxHeartbeats 1000000 in
private theorem exists_systemOverHom [IsFinite H.X.hom] (s : System (maximalIdeal A) H G) :
    ∃ f : H.X ⟶ G.X,
      ∀ n : ℕ, (Over.pullback (quotientMap (maximalIdeal A) n)).map f = (s.hom n).hom.hom := by
  let I := maximalIdeal A
  obtain ⟨f, hf, -⟩ :=
    existsUnique_adic_lift_of_isFinite H.X.hom (systemSchemeMap s) (systemSchemeMap_compatible s)
  have fw : f ≫ G.X.hom = H.X.hom := by
    apply adic_ext_of_isFiniteSource H.X.hom
    intro n
    let r := quotientMap I n
    let a := (s.hom n).hom.hom
    have ha : a.left ≫ pullback.snd G.X.hom r = pullback.snd H.X.hom r := a.w
    change finiteSourceReduction I H.X.hom n ≫ f ≫ G.X.hom =
      finiteSourceReduction I H.X.hom n ≫ H.X.hom
    rw [← Category.assoc, hf n]
    change (a.left ≫ pullback.fst G.X.hom r) ≫ G.X.hom =
      pullback.fst H.X.hom r ≫ H.X.hom
    rw [Category.assoc, pullback.condition, ← Category.assoc, ha, ← pullback.condition]
  let g : H.X ⟶ G.X := Over.homMk f fw
  refine ⟨g, fun n => ?_⟩
  let r := quotientMap I n
  let a := (s.hom n).hom.hom
  change (Over.pullback r).map g = a
  apply Over.OverMorphism.ext
  apply pullback.hom_ext
  · exact (overMap_fst g n).trans (hf n)
  · exact ((Over.pullback r).map g).w.trans a.w.symm

open CategoryTheory.Functor CategoryTheory.Functor.LaxMonoidal in
set_option maxHeartbeats 1000000 in
private theorem isMonHom_of_systemOverHom [IsFinite H.X.hom]
    (s : System (maximalIdeal A) H G) (f : H.X ⟶ G.X)
    (hf : ∀ n : ℕ, (Over.pullback (quotientMap (maximalIdeal A) n)).map f = (s.hom n).hom.hom) :
    IsMonHom f where
  one_hom := by
    have : IsFinite (𝟙_ (Over (Spec (CommRingCat.of A)))).hom :=
      inferInstanceAs (IsFinite (𝟙 (Spec (CommRingCat.of A))))
    apply over_adic_ext_of_isFiniteSource
    intro n
    let r := quotientMap (maximalIdeal A) n
    let P := Over.pullback r
    let H' := (baseChange r).obj H
    let G' := (baseChange r).obj G
    let a : H'.X ⟶ G'.X := (s.hom n).hom.hom
    have h : P.map f = a := hf n
    change P.map (η[H.X] ≫ f) = P.map η[G.X]
    apply (cancel_epi (ε P)).mp
    calc
      ε P ≫ P.map (η[H.X] ≫ f) = η[H'.X] ≫ a := by
        rw [P.map_comp, h, ← Category.assoc]
        rfl
      _ = η[G'.X] := IsMonHom.one_hom a
      _ = ε P ≫ P.map η[G.X] := rfl
  mul_hom := by
    have : IsFinite (H.X ⊗ H.X).hom := by rw [Over.tensorObj_hom]; infer_instance
    apply over_adic_ext_of_isFiniteSource
    intro n
    let r := quotientMap (maximalIdeal A) n
    let P := Over.pullback r
    let H' := (baseChange r).obj H
    let G' := (baseChange r).obj G
    let a : H'.X ⟶ G'.X := (s.hom n).hom.hom
    let c := LaxMonoidal.μ P H.X H.X
    have h : P.map f = a := hf n
    change P.map (μ[H.X] ≫ f) = P.map ((f ⊗ₘ f) ≫ μ[G.X])
    apply (cancel_epi c).mp
    calc
      c ≫ P.map (μ[H.X] ≫ f) = μ[H'.X] ≫ a := by
        rw [P.map_comp, h, ← Category.assoc]
        rfl
      _ = (a ⊗ₘ a) ≫ μ[G'.X] := IsMonHom.mul_hom a
      _ = c ≫ P.map ((f ⊗ₘ f) ≫ μ[G.X]) := by
        rw [P.map_comp]
        change _ = LaxMonoidal.μ P H.X H.X ≫ P.map (f ⊗ₘ f) ≫ P.map μ[G.X]
        rw [← μ_natural_assoc, h]
        rfl

/-- Restriction is bijective for an actual finite source group and an
arbitrary group-scheme target over a complete noetherian local ring. -/
def FiniteSourceAdicHomStatement : Prop :=
  ∀ (A : Type u) [CommRing A] [IsLocalRing A] [IsNoetherianRing A]
    [IsAdicComplete (maximalIdeal A) A]
    (H G : GroupScheme (Spec (CommRingCat.of A))) [IsFinite H.X.hom],
    Function.Bijective (System.restrict (maximalIdeal A) H G)

set_option maxHeartbeats 1000000 in
/-- The finite-source adic lift preserves the unit and product, which are
detected by restriction from the base and the finite two-fold source. -/
theorem finiteSourceAdicHom : FiniteSourceAdicHomStatement.{u} := by
  intro A _ _ _ _ H G _
  constructor
  · intro f g h
    apply Grp.hom_ext
    apply over_adic_ext_of_isFiniteSource
    intro n
    exact congrArg (fun s : System (maximalIdeal A) H G => (s.hom n).hom.hom) h
  · intro s
    obtain ⟨f, hf⟩ := exists_systemOverHom s
    have : IsMonHom f := isMonHom_of_systemOverHom s f hf
    refine ⟨Grp.homMk f, System.ext (fun n => ?_)⟩
    apply Grp.hom_ext
    exact hf n

end Langlands.GroupScheme.HomScheme.Adic
