import Langlands.AbelianScheme.PointedLawGroup
import Langlands.AbelianScheme.PointedLawHomScheme
import Langlands.AnthropicFLT.Theorems.Thm_AlgebraicGeometry_Scheme_Modules_ClosedImmersionBySections_pullback_fst_tensor_pullback_snd
import Langlands.AnthropicFLT.Theorems.Thm_AlgebraicGeometry_exists_isClosedImmersion_locallyOfFinitePresentation_iff_comp_eq_of_isSeparated

/-! # Representability of pointed abelian-scheme laws -/

noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open MonoidalCategory CartesianMonoidalCategory

namespace Langlands.AbelianScheme

universe u

namespace PointedLaw

variable {S : Scheme.{u}}

private theorem exists_equalizer {H E : Over S} [IsSeparated E.hom]
    [LocallyOfFinitePresentation E.hom] (a b : H ⟶ E) :
    ∃ (Z : Over S) (j : Z ⟶ H), IsClosedImmersion j.left ∧ LocallyOfFinitePresentation j.left ∧
      ∀ {T : Over S} (f : T ⟶ H), f ≫ a = f ≫ b ↔ ∃ i : T ⟶ Z, i ≫ j = f := by
  obtain ⟨W, j, hj, hfp, hW⟩ :=
    AlgebraicGeometry.exists_isClosedImmersion_locallyOfFinitePresentation_iff_comp_eq_of_isSeparated
      E.hom H.hom a.left b.left (Over.w a) (Over.w b)
  refine ⟨Over.mk (j ≫ H.hom), Over.homMk j rfl, hj, hfp inferInstance, ?_⟩
  intro T f
  constructor
  · intro hf
    obtain ⟨i, hi⟩ := (hW f.left).1 (congrArg Over.Hom.left hf)
    refine ⟨Over.homMk i ?_, Over.OverMorphism.ext hi⟩
    change i ≫ j ≫ H.hom = T.hom
    rw [← Category.assoc, hi, Over.w f]
  · rintro ⟨i, hi⟩
    exact Over.OverMorphism.ext ((hW f.left).2 ⟨i.left, congrArg Over.Hom.left hi⟩)

private theorem exists_equationLocus {H E : Over S} [IsSeparated E.hom]
    [LocallyOfFinitePresentation E.hom] (eqs : List ((H ⟶ E) × (H ⟶ E))) :
    ∃ (Z : Over S) (j : Z ⟶ H), IsClosedImmersion j.left ∧ LocallyOfFinitePresentation j.left ∧
      ∀ {T : Over S} (f : T ⟶ H), (∀ w ∈ eqs, f ≫ w.1 = f ≫ w.2) ↔
        ∃ i : T ⟶ Z, i ≫ j = f := by
  induction eqs with
  | nil =>
    refine ⟨H, 𝟙 H, inferInstanceAs (IsClosedImmersion (𝟙 H.left)),
      inferInstanceAs (LocallyOfFinitePresentation (𝟙 H.left)), ?_⟩
    intro T f
    simp
  | cons w eqs ih =>
    obtain ⟨Z₀, j₀, hj₀, hfp₀, h₀⟩ := ih
    obtain ⟨Z, j, hj, hfp, h⟩ := exists_equalizer (j₀ ≫ w.1) (j₀ ≫ w.2)
    refine ⟨Z, j ≫ j₀, inferInstanceAs (IsClosedImmersion (j.left ≫ j₀.left)),
      inferInstanceAs (LocallyOfFinitePresentation (j.left ≫ j₀.left)), ?_⟩
    intro T f
    constructor
    · intro hf
      obtain ⟨i₀, hi₀⟩ := (h₀ f).1 (fun v hv => hf v (List.mem_cons_of_mem w hv))
      have hi₀' : i₀ ≫ (j₀ ≫ w.1) = i₀ ≫ (j₀ ≫ w.2) := by
        simpa only [← Category.assoc, hi₀] using hf w (List.mem_cons_self ..)
      obtain ⟨i, hi⟩ := (h i₀).1 hi₀'
      exact ⟨i, by rw [← Category.assoc, hi, hi₀]⟩
    · rintro ⟨i, hi⟩
      have hi₀ : (i ≫ j) ≫ j₀ = f := (Category.assoc _ _ _).trans hi
      have hhead := (h (i ≫ j)).2 ⟨i, rfl⟩
      have htail := (h₀ f).2 ⟨i ≫ j, hi₀⟩
      intro v hv
      rcases List.mem_cons.mp hv with rfl | hv
      · simpa only [← Category.assoc, hi₀] using hhead
      · exact htail v hv

private theorem isHProjective_tensor {R : Type u} [CommRing R]
    {P Q : Over (Spec (CommRingCat.of R))}
    (hP : Langlands.AlgebraicGeometry.IsHProjective P.hom)
    (hQ : Langlands.AlgebraicGeometry.IsHProjective Q.hom) :
    Langlands.AlgebraicGeometry.IsHProjective (P ⊗ Q).hom := by
  let embeddings := @Langlands.AlgebraicGeometry.Picard.exists_closedImmersionBySections_iff_isHProjective R _
  obtain ⟨LP, hLP, hLP'⟩ := (embeddings P.hom).2 hP
  obtain ⟨LQ, hLQ, hLQ'⟩ := (embeddings Q.hom).2 hQ
  apply (embeddings (P ⊗ Q).hom).1
  refine ⟨_, Scheme.Modules.IsInvertible.tensor_monoidalV2
    (Scheme.Modules.IsInvertible.pullbackFLT (hL := hLP) (pullback.fst P.hom Q.hom))
    (Scheme.Modules.IsInvertible.pullbackFLT (hL := hLQ) (pullback.snd P.hom Q.hom)), ?_⟩
  exact Scheme.Modules.ClosedImmersionBySections.pullback_fst_tensor_pullback_snd
    P.hom Q.hom LP hLP' LQ hLQ'

section Equations

variable {X T U : Over S}

private abbrev Triple (X : Over S) : Over S := (X ⊗ X) ⊗ X

private def equationSides (e : 𝟙_ (Over S) ⟶ X) (L : Law X T) :
    List (((Triple X ⊗ T) ⟶ X) × ((Triple X ⊗ T) ⟶ X)) :=
  let p := fst (Triple X) T
  let x := p ≫ fst (X ⊗ X) X ≫ fst X X
  let y := p ≫ fst (X ⊗ X) X ≫ snd X X
  let z := p ≫ snd (X ⊗ X) X
  let a := snd (Triple X) T
  let m := L.mulAt a
  let i := L.invAt a
  let unit := toUnit _ ≫ e
  [(m (m x y) z, m x (m y z)), (m x y, m y x), (m unit x, x), (m (i x) x, unit)]

private theorem equationSides_restrict (e : 𝟙_ (Over S) ⟶ X) (L : Law X T) (f : U ⟶ T) :
    (equationSides e L).map (fun w => ((Triple X ◁ f) ≫ w.1, (Triple X ◁ f) ≫ w.2)) =
      equationSides e (L.restrict f) := by
  simp [equationSides, comp_toUnit_assoc]

private theorem equationSides_iff (e : 𝟙_ (Over S) ⟶ X) (L : Law X T) :
    (∀ w ∈ equationSides e L, w.1 = w.2) ↔ L.IsGroup e := by
  simp only [equationSides, List.forall_mem_cons, List.not_mem_nil, false_implies,
    implies_true, and_true]
  constructor
  · intro h U a
    let k (x y z : U ⟶ X) := lift (lift (lift x y) z) a
    refine ⟨fun x y z => ?_, fun x y => ?_, fun x => ?_, fun x => ?_⟩
    · simpa [k] using congrArg (k x y z ≫ ·) h.1
    · simpa [k] using congrArg (k x y x ≫ ·) h.2.1
    · simpa [k, comp_toUnit_assoc] using congrArg (k x x x ≫ ·) h.2.2.1
    · simpa [k, comp_toUnit_assoc] using congrArg (k x x x ≫ ·) h.2.2.2
  · intro h
    exact ⟨(h _).assoc _ _ _, (h _).comm _ _, (h _).leftUnit _, (h _).leftInv _⟩

end Equations

section ParameterScheme

variable {X T U : Over S}
variable (M : HomScheme (X ⊗ X) X) (I : HomScheme X X)

private def lawOfPoint (a : T ⟶ M.obj ⊗ I.obj) : Law X T :=
  ⟨M.eval (a ≫ fst M.obj I.obj), I.eval (a ≫ snd M.obj I.obj)⟩

private theorem lawOfPoint_comp (f : U ⟶ T) (a : T ⟶ M.obj ⊗ I.obj) :
    lawOfPoint M I (f ≫ a) = (lawOfPoint M I a).restrict f := by
  ext <;> simp [lawOfPoint, Law.restrict]

private theorem lawOfPoint_injective : Function.Injective (lawOfPoint M I (T := T)) := by
  intro f g h
  apply CartesianMonoidalCategory.hom_ext
  · exact (M.bijective T).1 (congrArg Law.mul h)
  · exact (I.bijective T).1 (congrArg Law.inv h)

private theorem lawOfPoint_surjective : Function.Surjective (lawOfPoint M I (T := T)) := by
  intro L
  refine ⟨lift (M.classify L.mul) (I.classify L.inv), ?_⟩
  ext <;> simp [lawOfPoint]

private theorem exists_lawLocus (e : 𝟙_ (Over S) ⟶ X) (E : HomScheme (Triple X) X) :
    ∃ (Z : Over S) (j : Z ⟶ M.obj ⊗ I.obj), IsClosedImmersion j.left ∧
      LocallyOfFinitePresentation j.left ∧
      ∀ {T : Over S} (f : T ⟶ M.obj ⊗ I.obj), (∃ i : T ⟶ Z, i ≫ j = f) ↔
        (lawOfPoint M I f).IsGroup e := by
  let L := lawOfPoint M I (𝟙 (M.obj ⊗ I.obj))
  let eqs := (equationSides e L).map (fun w => (E.classify w.1, E.classify w.2))
  let : IsSeparated E.obj.hom := E.separated
  let : LocallyOfFinitePresentation E.obj.hom := E.finitePresentation
  obtain ⟨Z, j, hj, hjfp, hj'⟩ := exists_equationLocus eqs
  refine ⟨Z, j, hj, hjfp, ?_⟩
  intro T f
  have hf : lawOfPoint M I f = L.restrict f := by
    simpa only [Category.comp_id] using lawOfPoint_comp M I f (𝟙 (M.obj ⊗ I.obj))
  rw [← hj', hf, ← equationSides_iff, ← equationSides_restrict]
  have classify_inj {a b : Triple X ⊗ T ⟶ X} : E.classify a = E.classify b ↔ a = b := by
    constructor
    · intro h
      simpa only [HomScheme.eval_classify] using congrArg (E.eval) h
    · exact congrArg E.classify
  simp only [eqs, List.forall_mem_map, HomScheme.comp_classify, classify_inj]

end ParameterScheme

end PointedLaw

open PointedLaw
open Langlands.AlgebraicGeometry

/-- Pointed abelian-scheme structures on the arbitrary base changes of the family are
    represented by a locally finitely presented monomorphism. -/
theorem pointedAbelianLawRepresentability : PointedAbelianLawRepresentabilityStatement.{u} := by
  intro R _ _ X p s g hs hp hsm hgc
  let S := Spec (CommRingCat.of R)
  let P : Over S := Over.mk p
  let e : 𝟙_ (Over S) ⟶ P := Over.homMk s hs
  let P₂ := P ⊗ P
  let P₃ := Triple P
  let : SmoothOfRelativeDimension g p := hsm
  let : Smooth p := SmoothOfRelativeDimension.smooth (n := g) p
  let : IsProper p := hp.isProper
  let : GeometricallyConnected p := hgc
  let : Smooth P.hom := ‹Smooth p›
  let : IsProper P.hom := ‹IsProper p›
  let : GeometricallyConnected P.hom := ‹GeometricallyConnected p›
  let : Smooth P₂.hom := inferInstanceAs (Smooth (pullback.fst p p ≫ p))
  let : Smooth P₃.hom := inferInstanceAs (Smooth (pullback.fst P₂.hom p ≫ P₂.hom))
  have hp₂ : IsHProjective P₂.hom := isHProjective_tensor hp hp
  have hp₃ : IsHProjective P₃.hom := isHProjective_tensor hp₂ hp
  obtain ⟨M⟩ := exists_homScheme hp₂ (show IsHProjective P.hom from hp)
  obtain ⟨I⟩ := exists_homScheme (show IsHProjective P.hom from hp) (show IsHProjective P.hom from hp)
  obtain ⟨E⟩ := exists_homScheme hp₃ (show IsHProjective P.hom from hp)
  obtain ⟨Z, j, hj, hjfp, hZ⟩ := exists_lawLocus M I e E
  let : LocallyOfFinitePresentation M.obj.hom := M.finitePresentation
  let : LocallyOfFinitePresentation I.obj.hom := I.finitePresentation
  let : LocallyOfFinitePresentation (M.obj ⊗ I.obj).hom := inferInstanceAs
    (LocallyOfFinitePresentation (pullback.fst M.obj.hom I.obj.hom ≫ M.obj.hom))
  have hfp : LocallyOfFinitePresentation Z.hom := by
    rw [← Over.w j]
    infer_instance
  let : Mono j.left := inferInstance
  refine ⟨Z.left, Z.hom, ?_, hfp, ?_⟩
  · constructor
    intro T f f' hff'
    let B : Over S := Over.mk (f ≫ Z.hom)
    let a : B ⟶ Z := Over.homMk f rfl
    let b : B ⟶ Z := Over.homMk f' hff'.symm
    have ha := (hZ (a ≫ j)).1 ⟨a, rfl⟩
    have hb := (hZ (b ≫ j)).1 ⟨b, rfl⟩
    have hh : a ≫ j = b ≫ j :=
      lawOfPoint_injective M I ((lawOfPoint M I (a ≫ j)).unique e ha hb)
    exact (cancel_mono j.left).1 (congrArg Over.Hom.left hh)
  · intro T t
    let B : Over S := Over.mk t
    rw [← exists_law_iff p s hs g t]
    constructor
    · rintro ⟨f, hf⟩
      let a : B ⟶ Z := Over.homMk f hf
      exact ⟨lawOfPoint M I (a ≫ j), (hZ (a ≫ j)).1 ⟨a, rfl⟩⟩
    · rintro ⟨L, hL⟩
      obtain ⟨a, rfl⟩ := lawOfPoint_surjective M I L
      obtain ⟨i, _⟩ := (hZ a).2 hL
      exact ⟨i.left, Over.w i⟩

end Langlands.AbelianScheme
