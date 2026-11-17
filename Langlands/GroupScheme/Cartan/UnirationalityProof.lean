import Langlands.GroupScheme.Cartan.UnirationalityStatement
import Langlands.GroupScheme.Cartan.GenerationProof
import Langlands.GroupScheme.Cartan.FiniteGeneration
import Langlands.GroupScheme.Reductive.TorusDominationReduction
import Langlands.AlgebraicGeometry.PointTopology.UnirationalProducts

/-! # Unirationality from unirational Cartan subgroups -/

noncomputable section

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open CategoryTheory.MonoidalCategory CategoryTheory.CartesianMonoidalCategory
open Langlands.AlgebraicGeometry.PointTopology
open scoped CategoryTheory.MonObj

namespace Langlands.GroupScheme

/-- A finite generating family of smooth connected affine unirational groups
makes its ambient smooth affine group unirational. -/
private theorem isUnirational_of_finite_generating_family
    {k : Type u} [Field k] (G : GroupScheme (Spec (CommRingCat.of k)))
    [Smooth G.X.hom] [IsAffineHom G.X.hom]
    {m : ℕ} (A : Fin m → GroupScheme (Spec (CommRingCat.of k)))
    (a : ∀ j, A j ⟶ G)
    (hA : ∀ j, Smooth (A j).X.hom ∧ IsAffineHom (A j).X.hom ∧
      ConnectedSpace (A j).X.left)
    (hU : ∀ j, IsUnirational k (A j).X)
    (hgen : ∀ (H : GroupScheme (Spec (CommRingCat.of k))) (i : H ⟶ G),
      IsClosedSubgroup i → (∀ j, FactorsThrough (a j).hom.hom i) →
        SubgroupFunctor.range i = ⊤) :
    IsUnirational k G.X := by
  classical
  let A' : ULift.{u} (Fin m) → GroupScheme (Spec (CommRingCat.of k)) := fun j => A j.down
  let P : GroupScheme (Spec (CommRingCat.of k)) := pi A'
  have hgood : ∀ j, ImageGeneration.FinitePowerGood _ (A' j).X := by
    intro j
    have : Smooth (A j.down).X.hom := (hA j.down).1
    exact ImageGeneration.finitePowerGood_of_geometricallyIntegral (A' j).X
      (hA j.down).2.1 inferInstance
      (smoothConnectedAffineGeometry.1 k (A j.down) (hA j.down).1
        (hA j.down).2.1 (hA j.down).2.2)
  have hPgood : ImageGeneration.FinitePowerGood _ P.X := by
    have : (ImageGeneration.FinitePowerGood (Spec (CommRingCat.of k))).IsClosedUnderFiniteProducts :=
      ObjectProperty.IsClosedUnderFiniteProducts.mk'
    exact ObjectProperty.prop_of_isLimit_fan _ (piIsLimit A') hgood
  have : GeometricallyReduced P.X.hom := hPgood.2.2.1
  have : GeometricallyIrreducible P.X.hom := hPgood.2.2.2
  have hPint : GeometricallyIntegral P.X.hom :=
    GeometricallyIntegral.of_geometricallyReduced_of_geometricallyIrreducible P.X.hom
  have hPU : IsUnirational k P.X :=
    isUnirational_of_isLimit_fan k (piIsLimit A') fun j => hU j.down
  let π' : ∀ j : Fin m, P.X ⟶ (A j).X := fun j => (Pi.π A' ⟨j⟩).hom.hom
  let f : P.X ⟶ G.X := (List.ofFn fun j : Fin m => π' j ≫ (a j).hom.hom).prod
  have hv₀ : (1 : Over.mk (𝟙 (Spec (CommRingCat.of k))) ⟶ P.X) ≫ f = 1 := by
    rw [comp_list_prod, List.map_ofFn]
    refine List.prod_eq_one (List.forall_mem_ofFn_iff.2 fun j => ?_)
    simp only [Function.comp_apply, π', MonObj.one_comp]
  obtain ⟨D, -, -, -, n, -, hdom⟩ :=
    ImageGeneration.pointedImageGeneration k G inferInstance inferInstance P.X
      hPgood.1 hPgood.2.1 hPint 1 f hv₀
  let s : ∀ j : Fin m, (A j).X ⟶ P.X := fun j =>
    (piPointsEquiv A' (A j).X).symm
      (Pi.mulSingle (M := fun i : ULift.{u} (Fin m) => (A j).X ⟶ (A' i).X)
        ⟨j⟩ (𝟙 (A j).X))
  have hs : ∀ j, s j ≫ f = (a j).hom.hom := by
    intro j
    rw [comp_list_prod, List.map_ofFn, prod_ofFn_eq_of_eq_one _ j]
    · simp only [Function.comp_apply, π', s, ← Category.assoc, piPointsEquiv_symm_π,
        Pi.mulSingle_eq_same, Category.id_comp]
    · intro i hi
      have hne : (⟨i⟩ : ULift.{u} (Fin m)) ≠ ⟨j⟩ := fun e => hi (congrArg ULift.down e)
      simp only [Function.comp_apply, π', s, ← Category.assoc, piPointsEquiv_symm_π,
        Pi.mulSingle_eq_of_ne hne, MonObj.one_comp]
  have hfac : ∀ j, FactorsThrough (a j).hom.hom D.inclusion := fun j =>
    ⟨s j ≫ D.factor, by rw [Category.assoc, D.factor_comp, hs j]⟩
  have htop := hgen D.group D.inclusion D.closed hfac
  obtain ⟨r, hr⟩ : ∃ r : G.X ⟶ D.group.X, r ≫ D.inclusion.hom.hom = 𝟙 G.X :=
    SubgroupFunctor.mem_range.1 (by rw [htop]; exact Subgroup.mem_top _)
  have hsurj : Function.Surjective D.inclusion.hom.hom.left := fun x =>
    ⟨r.left x, by rw [← Scheme.Hom.comp_apply, ← Over.comp_left, hr]; rfl⟩
  have hpowU : IsUnirational k (finitePower P.X n) :=
    isUnirational_pi k (fun _ : Fin n => P.X) fun _ => hPU
  exact (hpowU.map (D.powerMap n) hdom.denseRange).map D.inclusion.hom.hom hsurj.denseRange

/-- Milne, Corollary 17.92: a smooth connected affine group over an infinite
field is unirational when all of its actual Cartan subgroups are unirational. -/
theorem cartanUnirationalityStatement : CartanUnirationalityStatement.{u} := by
  intro k _ _ G hsm haff hconn hU
  classical
  let : Smooth G.X.hom := hsm
  let : IsAffineHom G.X.hom := haff
  let : ConnectedSpace G.X.left := hconn
  let A : CartanSubgroup G → GroupScheme (Spec (CommRingCat.of k)) := fun C => C.group
  let a : ∀ C : CartanSubgroup G, A C ⟶ G := fun C => C.inclusion
  have hA : ∀ C : CartanSubgroup G,
      Smooth (A C).X.hom ∧ IsAffineHom (A C).X.hom ∧ ConnectedSpace (A C).X.left := by
    intro C
    refine ⟨C.isCartan.smooth_connected.1, ?_, C.isCartan.smooth_connected.2⟩
    let : IsClosedImmersion (a C).hom.hom.left := C.isCartan.1
    change IsAffineHom C.group.X.hom
    rw [← Over.w C.inclusion.hom.hom]
    infer_instance
  have hall : ∀ (H : GroupScheme (Spec (CommRingCat.of k))) (i : H ⟶ G),
      IsClosedSubgroup i → (∀ C : CartanSubgroup G, FactorsThrough (a C).hom.hom i) →
        SubgroupFunctor.range i = ⊤ := by
    intro H i hi hfamily
    apply cartanGenerationStatement k G hsm haff hconn H i hi
    intro C c hc
    exact hfamily ⟨C, c, hc⟩
  obtain ⟨s, hs⟩ := FiniteGeneration.exists_finite_generating_subfamily_of_pointedImageGeneration
    (A := A) (a := a) ImageGeneration.pointedImageGeneration hA hall
  let e : Fin (Fintype.card s) ≃ s := (Fintype.equivFin s).symm
  apply isUnirational_of_finite_generating_family G (fun j => A (e j).val)
    (fun j => a (e j).val) (fun j => hA (e j).val)
    (fun j => hU (e j).val.group (e j).val.inclusion (e j).val.isCartan)
  intro H i hi hfamily
  apply hs H i hi
  intro C hC
  have h := hfamily (e.symm ⟨C, hC⟩)
  change FactorsThrough (a (e (e.symm ⟨C, hC⟩)).val).hom.hom i at h
  rw [e.apply_symm_apply] at h
  exact h

end Langlands.GroupScheme
