import Langlands.AlgebraicGeometry.GenericPointAvoidance
import Langlands.AlgebraicGeometry.HenselianBirationalSolution.Extension
import Langlands.AlgebraicGeometry.HenselianBirationalSolution.Density

/-! # Generic points and agreement of morphisms

The generic points of the irreducible components of a scheme are its points without proper
generizations. Every point specializes from one of them, so an open set containing all of them is
dense, and two morphisms from a reduced scheme to a separated scheme agreeing on such an open set
are equal. Generalizing maps (open immersions, flat morphisms) preserve generic points, and sets
dense in the fibres of a morphism contain them.

The module also restates the extension lemma of `Extension` for local pieces given by open
immersions, with agreement required only on an open subset containing the generic points.
-/

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Topology TopologicalSpace

noncomputable section

namespace Langlands.AlgebraicGeometry.HenselianBirationalSolution

theorem mem_genericPoints_iff_scheme {X : Scheme.{u}} {x : X} :
    x ∈ genericPoints X ↔ ∀ y : X, y ⤳ x → y = x :=
  GenericPointAvoidance.mem_genericPoints_iff

/-- Every point of a scheme specializes from a generic point of an irreducible component. -/
theorem exists_genericPoints_specializes (X : Scheme.{u}) (x : X) :
    ∃ y ∈ genericPoints X, y ⤳ x := by
  let C : irreducibleComponents X :=
    ⟨irreducibleComponent x, irreducibleComponent_mem_irreducibleComponents x⟩
  exact ⟨(genericPoints.ofComponent C).1, (genericPoints.ofComponent C).2,
    (genericPoints.isGenericPoint_ofComponent C).specializes mem_irreducibleComponent⟩

/-- A set dense in the fibres of a morphism contains the generic points. -/
theorem FibreGenerizationDense.genericPoints_subset {X S : Scheme.{u}} {q : X ⟶ S}
    {W : Set X} (h : FibreGenerizationDense q W) : genericPoints X ⊆ W := by
  intro x hx
  obtain ⟨y, hy, -, hyx⟩ := h x
  rwa [mem_genericPoints_iff_scheme.mp hx y hyx] at hy

/-- Generalizing maps preserve generic points. -/
theorem mapsTo_genericPoints {X Y : Scheme.{u}} (f : X ⟶ Y) (hf : GeneralizingMap f) :
    Set.MapsTo f (genericPoints X) (genericPoints Y) := by
  intro x hx
  rw [mem_genericPoints_iff_scheme] at hx ⊢
  intro y hy
  obtain ⟨x', hx', rfl⟩ := hf hy
  rw [hx x' hx']

/-- Open immersions are generalizing. -/
theorem generalizingMap_of_isOpenImmersion {X Y : Scheme.{u}} (f : X ⟶ Y) [IsOpenImmersion f] :
    GeneralizingMap f :=
  f.isOpenEmbedding.generalizingMap

/-- Flat morphisms are generalizing. -/
theorem generalizingMap_of_flat {X Y : Scheme.{u}} (f : X ⟶ Y) [Flat f] : GeneralizingMap f :=
  Flat.generalizingMap f

/-- The preimage of a set containing the generic points under a generalizing map contains the
generic points. -/
theorem genericPoints_subset_preimage {X Y : Scheme.{u}} (f : X ⟶ Y) (hf : GeneralizingMap f)
    {W : Set Y} (hW : genericPoints Y ⊆ W) : genericPoints X ⊆ f ⁻¹' W :=
  fun _ hx => hW (mapsTo_genericPoints f hf hx)

/-- A set containing the generic points contains a generization of every point. -/
theorem exists_specializes_of_genericPoints_subset {X : Scheme.{u}} {W : Set X}
    (hW : genericPoints X ⊆ W) (x : X) : ∃ y ∈ W, y ⤳ x := by
  obtain ⟨y, hy, hyx⟩ := exists_genericPoints_specializes X x
  exact ⟨y, hW hy, hyx⟩

/-- A set containing the generic points is dense. -/
theorem dense_of_genericPoints_subset {X : Scheme.{u}} {W : Set X} (hW : genericPoints X ⊆ W) :
    Dense W := by
  intro x
  obtain ⟨y, hy, hyx⟩ := exists_specializes_of_genericPoints_subset hW x
  exact closure_mono (Set.singleton_subset_iff.mpr hy) (specializes_iff_mem_closure.mp hyx)

/-- The inclusion of an open set containing the generic points is dominant. -/
theorem isDominant_of_genericPoints_subset {X : Scheme.{u}} (W : X.Opens)
    (hW : genericPoints X ⊆ W) : IsDominant W.ι :=
  ⟨by rw [DenseRange, Scheme.Opens.range_ι]; exact dense_of_genericPoints_subset hW⟩

/-- Morphisms from a reduced scheme to a separated scheme agreeing on an open set containing
the generic points are equal. -/
theorem ext_of_genericPoints_subset {X Z : Scheme.{u}} [IsReduced X] [Z.IsSeparated]
    {φ ψ : X ⟶ Z} (W : X.Opens) (hW : genericPoints X ⊆ W) (h : W.ι ≫ φ = W.ι ≫ ψ) : φ = ψ := by
  have := isDominant_of_genericPoints_subset W hW
  exact ext_of_isDominant W.ι h

/-- Relative version of `ext_of_genericPoints_subset`. -/
theorem ext_of_genericPoints_subset_of_isSeparated {X Z S : Scheme.{u}} [IsReduced X]
    (s : Z ⟶ S) [IsSeparated s] {φ ψ : X ⟶ Z} (hs : φ ≫ s = ψ ≫ s) (W : X.Opens)
    (hW : genericPoints X ⊆ W) (h : W.ι ≫ φ = W.ι ≫ ψ) : φ = ψ := by
  have := isDominant_of_genericPoints_subset W hW
  exact ext_of_isDominant_of_isSeparated s hs W.ι h

/-- Agreement on an open part `W` of `O`, dense in `O`, implies agreement everywhere. -/
theorem AgreesOn.of_dense' {X Z : Scheme.{u}} [IsReduced X] [Z.IsSeparated] {D O W : X.Opens}
    (hD : Dense (D : Set X)) {θ : D.toScheme ⟶ Z} {φ : O.toScheme ⟶ Z} (hW : W ≤ O)
    (hd : (O : Set X) ⊆ closure (W : Set X)) (h : AgreesOn θ φ W) :
    AgreesOn θ φ Set.univ := by
  refine AgreesOn.of_dense (W := W ⊓ D) (inf_le_inf_right D hW) ?_ ?_
  · refine hd.trans (closure_minimal ?_ isClosed_closure)
    exact hD.open_subset_closure_inter W.isOpen
  · intro T u v huv hr
    exact h T u v huv (hr.trans inf_le_left)

/-- **Extension from local pieces given by open immersions.** Let `X` be reduced, `Z` separated
and `θ` a morphism on a dense open `D`. Suppose that every point of `X` lies in the image of an
open immersion `e : Q ⟶ X` carrying a morphism `φ : Q ⟶ Z` which agrees with `θ` at all points
of an open `W ⊆ Q` containing the generic points of `Q`. Then `θ` extends to `X`. -/
theorem exists_extension_of_pieces {X Z : Scheme.{u}} [IsReduced X] [Z.IsSeparated]
    (D : X.Opens) (hD : Dense (D : Set X)) (θ : D.toScheme ⟶ Z)
    (pieces : ∀ x : X, ∃ (Q : Scheme.{u}) (e : Q ⟶ X) (_ : IsOpenImmersion e) (φ : Q ⟶ Z)
      (W : Q.Opens), x ∈ Set.range e ∧ genericPoints Q ⊆ W ∧
      ∀ (T : Scheme.{u}) (u : T ⟶ W.toScheme) (v : T ⟶ D.toScheme),
        u ≫ W.ι ≫ e = v ≫ D.ι → u ≫ W.ι ≫ φ = v ≫ θ) :
    ∃ Φ : X ⟶ Z, D.ι ≫ Φ = θ := by
  apply exists_extension D hD θ
  intro x
  obtain ⟨Q, e, he, φ, W, hx, hgen, hag⟩ := pieces x
  refine ⟨e.opensRange, e.isoOpensRange.inv ≫ φ, hx, ?_⟩
  have hle : e ''ᵁ W ≤ e.opensRange := by
    rintro _ ⟨q, -, rfl⟩
    exact ⟨q, rfl⟩
  refine AgreesOn.of_dense' hD hle ?_ ?_
  · rintro _ ⟨q, rfl⟩
    obtain ⟨q', hq', hq'q⟩ := exists_specializes_of_genericPoints_subset hgen q
    have h1 : e q ∈ closure {e q'} := specializes_iff_mem_closure.mp (hq'q.map e.continuous)
    have h2 : e q' ∈ (e ''ᵁ W : Set X) := ⟨q', hq', rfl⟩
    exact closure_mono (Set.singleton_subset_iff.mpr h2) h1
  · intro T u v huv hr
    set u' := u ≫ e.isoOpensRange.inv
    have hu' : u' ≫ e = u ≫ e.opensRange.ι := by
      rw [Category.assoc, Scheme.Hom.isoOpensRange_inv_comp]
    have hrW : Set.range u' ⊆ Set.range W.ι := by
      rintro _ ⟨t, rfl⟩
      rw [Scheme.Opens.range_ι]
      obtain ⟨q, hq, hqe⟩ := hr ⟨t, rfl⟩
      have : q = u' t := by
        apply e.isOpenEmbedding.injective
        rw [← Scheme.Hom.comp_apply, hu']
        exact hqe
      rw [← this]
      exact hq
    set w := IsOpenImmersion.lift W.ι u' hrW
    have hw : w ≫ W.ι = u' := IsOpenImmersion.lift_fac _ _ _
    have := hag T w v (by rw [reassoc_of% hw, hu', huv])
    rw [reassoc_of% hw] at this
    rw [← Category.assoc]
    exact this

/-- A scheme separated over a separated scheme is separated. -/
theorem isSeparated_of_isSeparated {X S : Scheme.{u}} (f : X ⟶ S) [IsSeparated f]
    [S.IsSeparated] : X.IsSeparated :=
  ⟨by rw [← terminal.comp_from f]; infer_instance⟩

end Langlands.AlgebraicGeometry.HenselianBirationalSolution
