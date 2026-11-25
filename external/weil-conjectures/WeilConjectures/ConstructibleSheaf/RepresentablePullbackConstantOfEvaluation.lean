/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.AlgebraicGeometry.EtaleSheaves
public import WeilConjectures.AlgebraicGeometry.FundamentalGroup.FiniteEtale
public import WeilConjectures.Mathlib.AlgebraicGeometry.Sites.Proetale
import WeilConjectures.AlgebraicGeometry.FundamentalGroup.Connected
import WeilConjectures.AlgebraicGeometry.Sites.InverseImageRepresentable
import Mathlib.CategoryTheory.Sites.LocallyBijective
import WeilConjectures.AlgebraicGeometry.FundamentalGroup.ConstantCover
import WeilConjectures.AlgebraicGeometry.FundamentalGroup.Functoriality

/-!
# Constancy of a representable inverse image from exhaustive sections

Source: Stacks Project, Section 03SF and Tags 03P5, 0DV6.
(blueprint: lem-weil-pbc-representable-pullback-constant-evaluation)
-/

@[expose] public section

set_option autoImplicit false
universe u
open CategoryTheory CategoryTheory.Limits Opposite
namespace AlgebraicGeometry.Scheme.FiniteEtale

/-- If all points of a finite etale fibre are represented uniquely by maps from a
connected cover, the representable sheaf becomes constant on that cover.
Source: Stacks Project, Section 03SF and Tags 03P5, 0DV6.
(blueprint: lem-weil-pbc-representable-pullback-constant-evaluation)

Proof: each map A -> P gives its graph as a section of A times_U P -> A. Form the map
from the coproduct of copies of A indexed by Hom_U(A,P) to A times_U P, using these
sections. This index set is finite because A is connected. On the geometric fibre
at the point a of A this map is the evaluation map in the hypothesis, so it is a
bijection. The fibre functor on finite etale A-schemes reflects isomorphisms; hence
this map is an isomorphism. The sheaf represented by a coproduct of copies of A is
the constant sheaf with value ULift Hom_U(A,P): maps into it are locally constant
choices of a summand. The inverse-image/representable comparison identifies the
sheaf represented by A times_U P with the inverse image in the conclusion.
If P has empty fibre, the index set and the coproduct are empty and the same argument
identifies the inverse image with the constant empty sheaf. -/
theorem representable_pullback_isConstant_of_evaluation_bijective
    {U : Scheme.{u}} [ConnectedSpace U]
    {Ω : Type u} [Field Ω] [IsAlgClosed Ω] (s : Spec (.of Ω) ⟶ U)
    (A P : U.FiniteEtale) [ConnectedSpace A.obj.left]
    (a : (fiber s).obj A)
    (h : Function.Bijective (fun f : A ⟶ P ↦ (fiber s).map f a)) :
    ((etaleSetPullback A.obj.hom).obj
      (U.smallEtaleTopology.uliftYoneda.{u + 1}.obj P.obj)).IsConstant
        A.obj.left.smallEtaleTopology := by
  classical
  have : PreGaloisCategory.IsConnected A := isConnected_of_connectedSpace A
  let I := A ⟶ P
  let B := A.obj.left
  let R : B.FiniteEtale := (FiniteEtale.pullback A.obj.hom).obj P
  let σ (i : I) : B ⟶ R.obj.left :=
    Limits.pullback.lift i.hom.left (𝟙 B) (hom_left_comp i)
  have hσ (i : I) : σ i ≫ R.obj.hom = 𝟙 B := by
    exact Limits.pullback.lift_snd _ _ _
  let d : (∐ fun _ : I ↦ B) ⟶ B := Sigma.desc fun _ ↦ 𝟙 B
  have : Etale d := IsZariskiLocalAtSource.sigmaDesc fun _ ↦ inferInstance
  let D : B.FiniteEtale := ⟨Etale.mk d, inferInstanceAs (IsFinite d)⟩
  let g : D ⟶ R := ObjectProperty.homMk
    (MorphismProperty.Over.homMk (Sigma.desc σ) (Sigma.hom_ext _ _ fun i ↦ by
      simp [hσ, D, d]))
  let t : Spec (.of Ω) ⟶ B := a.left
  have ht : t ≫ A.obj.hom = s := fiber_left_comp s a
  have hg : IsIso ((fiber t).map g) := by
    rw [ConcreteCategory.isIso_iff_bijective]
    constructor
    · intro z w hzw
      have : Subsingleton (Spec (.of Ω)) := inferInstanceAs (Subsingleton (PrimeSpectrum Ω))
      have : Nonempty (Spec (.of Ω)) := inferInstanceAs (Nonempty (PrimeSpectrum Ω))
      obtain ⟨i, z', hz'⟩ := exists_comp_sigmaι_eq_of_subsingleton
        (show Spec (.of Ω) ⟶ _ from z.left)
      obtain ⟨j, w', hw'⟩ := exists_comp_sigmaι_eq_of_subsingleton
        (show Spec (.of Ω) ⟶ _ from w.left)
      change z' ≫ Sigma.ι (fun _ : I ↦ B) i = z.left at hz'
      change w' ≫ Sigma.ι (fun _ : I ↦ B) j = w.left at hw'
      have hz : z' = t := by
        have hz := fiber_left_comp t z
        rw [← hz', Category.assoc] at hz
        simpa [D, d] using hz
      have hw : w' = t := by
        have hw := fiber_left_comp t w
        rw [← hw', Category.assoc] at hw
        simpa [D, d] using hw
      have hij : i = j := h.1 (fiber_ext s (by
        have hh := congrArg (fun q ↦ q.left ≫ Limits.pullback.fst P.obj.hom A.obj.hom) hzw
        change (z.left ≫ Sigma.desc σ) ≫ _ = (w.left ≫ Sigma.desc σ) ≫ _ at hh
        rw [← hz', ← hw', hz, hw] at hh
        simpa only [fiber_map_left, Category.assoc, Sigma.ι_comp_desc_assoc, σ,
          Limits.pullback.lift_fst, t] using hh))
      exact fiber_ext t (by rw [← hz', ← hw', hz, hw, hij])
    · intro z
      let y : (fiber s).obj P :=
        fiberMk s P (z.left ≫ Limits.pullback.fst P.obj.hom A.obj.hom) (by
          rw [Category.assoc, Limits.pullback.condition, ← Category.assoc]
          exact (congrArg (· ≫ A.obj.hom) (fiber_left_comp t z)).trans ht)
      obtain ⟨i, hi⟩ := h.2 y
      have hi' : t ≫ i.hom.left = z.left ≫ Limits.pullback.fst P.obj.hom A.obj.hom :=
        congrArg (fun q ↦ q.left) hi
      refine ⟨fiberMk t D (t ≫ Sigma.ι (fun _ : I ↦ B) i) (by simp [D, d]),
        fiber_ext t ?_⟩
      change (t ≫ Sigma.ι (fun _ : I ↦ B) i) ≫ Sigma.desc σ = z.left
      apply Limits.pullback.hom_ext
      · simpa [σ] using hi'
      · simpa [σ, R, FiniteEtale.pullback] using (fiber_left_comp t z).symm
  have : IsIso g := isIso_of_reflects_iso g (fiber t)
  let H := B.smallEtaleTopology.uliftYoneda.{u + 1}.obj D.obj
  let κ : (Functor.const B.Etaleᵒᵖ).obj (ULift.{u + 1} I) ⟶ H.obj :=
    { app W := ↾(fun i ↦ ⟨MorphismProperty.Over.homMk
        (W.unop.hom ≫ Sigma.ι (fun _ : I ↦ B) i.down) (by simp [D, d])⟩)
      naturality W V f := by
        ext i
        apply ULift.ext
        apply MorphismProperty.Over.Hom.ext
        change V.unop.hom ≫ Sigma.ι (fun _ : I ↦ B) i.down =
          f.unop.left ≫ W.unop.hom ≫ Sigma.ι (fun _ : I ↦ B) i.down
        rw [← Category.assoc, MorphismProperty.Over.w] }
  have hinj : Presheaf.IsLocallyInjective B.smallEtaleTopology κ := by
    refine ⟨?_⟩
    intro W i j hij
    by_cases hIJ : i = j
    · subst hIJ
      exact B.smallEtaleTopology.superset_covering (fun _ _ _ ↦ rfl)
        (B.smallEtaleTopology.top_mem _)
    · have : IsEmpty W.unop.left := ⟨fun x ↦ hIJ (ULift.ext (by
        have he := congrArg (fun v ↦ v.down.left x) hij
        exact congrArg Sigma.fst ((sigmaι_eq_iff (fun _ : I ↦ B) _ _ _ _).mp he)))⟩
      refine B.smallEtaleTopology.superset_covering ?_
        ((ofArrows_mem_smallEtaleTopology_iff (Z := PEmpty.elim) (W := W.unop)
          (fun i : PEmpty.{1} ↦ i.elim)).2 (Set.eq_univ_of_forall fun x ↦ isEmptyElim x))
      rw [Sieve.ofArrows, Sieve.generate_le_iff]
      rintro _ _ ⟨i⟩
      exact i.elim
  have hsurj : Presheaf.IsLocallySurjective B.smallEtaleTopology κ := by
    refine ⟨?_⟩
    intro W r
    let V (i : I) : B.Etale := Etale.mk
      (Limits.pullback.fst r.down.left (Sigma.ι (fun _ : I ↦ B) i) ≫ W.hom)
    let ι (i : I) : V i ⟶ W := MorphismProperty.Over.homMk
      (Limits.pullback.fst r.down.left (Sigma.ι (fun _ : I ↦ B) i)) rfl
    refine B.smallEtaleTopology.superset_covering ?_
      ((ofArrows_mem_smallEtaleTopology_iff ι).2 ?_)
    · rw [Sieve.ofArrows, Sieve.generate_le_iff]
      rintro _ _ ⟨i⟩
      refine ⟨⟨i⟩, ?_⟩
      apply ULift.ext
      apply MorphismProperty.Over.Hom.ext
      change (Limits.pullback.fst r.down.left (Sigma.ι (fun _ : I ↦ B) i) ≫
        W.hom) ≫ Sigma.ι (fun _ : I ↦ B) i =
          Limits.pullback.fst r.down.left (Sigma.ι (fun _ : I ↦ B) i) ≫ r.down.left
      have hr : r.down.left ≫ d = W.hom := MorphismProperty.Over.w r.down
      have hπ : Limits.pullback.fst r.down.left (Sigma.ι (fun _ : I ↦ B) i) ≫
          W.hom = Limits.pullback.snd r.down.left (Sigma.ι (fun _ : I ↦ B) i) := by
        rw [← hr, ← Category.assoc, Limits.pullback.condition, Category.assoc]
        simp [d]
      rw [hπ, Limits.pullback.condition]
    · refine Set.eq_univ_of_forall fun x ↦ ?_
      obtain ⟨i, y, hy⟩ := (sigmaOpenCover fun _ : I ↦ B).exists_eq (r.down.left x)
      obtain ⟨z, hz, -⟩ := Scheme.Pullback.exists_preimage_pullback x y hy.symm
      exact Set.mem_iUnion.2 ⟨i, z, hz⟩
  let k : (constantSheaf B.smallEtaleTopology (Type (u + 1))).obj (ULift.{u + 1} I) ⟶ H :=
    ((sheafificationAdjunction B.smallEtaleTopology (Type (u + 1))).homEquiv _ _).symm κ
  have hk : toSheafify B.smallEtaleTopology _ ≫ k.hom = κ := by
    have hk := ((sheafificationAdjunction B.smallEtaleTopology (Type (u + 1))).homEquiv
      ((Functor.const B.Etaleᵒᵖ).obj (ULift.{u + 1} I)) H).apply_symm_apply κ
    rw [Adjunction.homEquiv_unit, sheafificationAdjunction_unit_app] at hk
    exact hk
  have : IsIso k := (Sheaf.isLocallyBijective_iff_isIso k).mp ⟨by
      change Presheaf.IsLocallyInjective _ _
      rw [← Presheaf.comp_isLocallyInjective_iff _ (toSheafify B.smallEtaleTopology _), hk]
      exact hinj, by
      change Presheaf.IsLocallySurjective _ _
      rw [← Presheaf.comp_isLocallySurjective_iff _ (toSheafify B.smallEtaleTopology _), hk]
      exact hsurj⟩
  have hH : H.IsConstant B.smallEtaleTopology :=
    Sheaf.isConstant_of_iso _ (asIso k).symm
  have hR : (B.smallEtaleTopology.uliftYoneda.{u + 1}.obj R.obj).IsConstant
      B.smallEtaleTopology :=
    @Sheaf.isConstant_congr _ _ _ _ _ _ _ _
      (B.smallEtaleTopology.uliftYoneda.mapIso
        ((ObjectProperty.ι _).mapIso (asIso g))) hH
  have : A.obj.hom.Etale.IsContinuous U.smallEtaleTopology B.smallEtaleTopology :=
    Hom.isContinuous_etale A.obj.hom
  obtain ⟨η⟩ := nonempty_inverseImage_representable_iso.{u, u + 1} A.obj.hom
    (etaleSetPullback A.obj.hom)
    (Functor.sheafPullbackConstruction.sheafAdjunctionContinuous A.obj.hom.Etale
      (Type (u + 1)) U.smallEtaleTopology B.smallEtaleTopology)
  exact @Sheaf.isConstant_congr _ _ _ _ _ _ _ _ (η.app P.obj).symm hR

end AlgebraicGeometry.Scheme.FiniteEtale
