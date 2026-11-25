/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.ProjectiveBundleQuotientGeometry.ProjectiveBundleQuotientData
public import WeilConjectures.AlgebraicGeometry.RelativeProj.BaseChange
public import WeilConjectures.AlgebraicGeometry.Modules.TensorSection
import WeilConjectures.AlgebraicGeometry.SymmetricProjTautologicalCharts.SymmetricProjPullbackNormalizedChartFactor
import all WeilConjectures.AlgebraicGeometry.ProjectiveBundleQuotientGeometry.LineQuotientPulledChartNormalization

/-! Local `q'` coefficient frames for the normalized pullback generator relation.

Source: Stacks Project, Constructions, Tags 01N2, 01NQ, 01NR and 01OB.
The statement isolates the second (normalized) quotient formula after a local
frame and coefficient formula for `q` have been chosen.
(blueprint: lem-trf-symmetric-proj-pullback-generator-local-coefficients-qprime)
-/
@[expose] public section
set_option autoImplicit false
set_option relaxedAutoImplicit false
universe u
open CategoryTheory CategoryTheory.Limits Opposite
open scoped AlgebraicGeometry
namespace AlgebraicGeometry.SymmetricProjTautologicalCharts
attribute [local instance 2000] CategoryTheory.Abelian.hasFiniteLimits
attribute [local irreducible] Scheme.Modules.tensorPullback Scheme.Modules.tensorPullbackObj
  Scheme.Modules.tensorPullbackSectionComp Scheme.Modules.tensorPullbackSectionAdjunction
  Scheme.GradedAlgebraData.relProj Scheme.GradedAlgebraData.relProjι
  Scheme.GradedAlgebraData.relProjHom
  Scheme.GradedAlgebraData.PullbackData.relProjComparison
  Scheme.Modules.tensorPullbackSection

open Scheme.Modules

private theorem tensor_unit_section {Y Z : Scheme.{u}} (f : Y ⟶ Z)
    (M : Z.Modules) (U : Z.Opens) (s : Γ(M, U)) :
    ((tensorPullbackSectionAdjunction f).unit.app M).app U s =
      tensorPullbackSection f M U s := by
  unfold tensorPullbackSectionAdjunction
  exact (Classical.choose_spec (existsUnique_tensorPullbackSectionAdjunction f)).1 M U s

private theorem tensor_section_map {Y Z : Scheme.{u}} (f : Y ⟶ Z)
    {M N : Z.Modules} (v : M ⟶ N) (U : Z.Opens) (s : Γ(M, U)) :
    ((tensorPullback f).map v).app (f ⁻¹ᵁ U) (tensorPullbackSection f M U s) =
      tensorPullbackSection f N U (v.app U s) := by
  rw [← tensor_unit_section, ← tensor_unit_section]
  exact congrArg (fun k ↦ k.app U s)
    ((tensorPullbackSectionAdjunction f).unit_naturality v)

private theorem tensor_hom_ext_cover {Y : Scheme.{u}} {I : Type u}
    {Z : I → Scheme.{u}} (j : ∀ i, Z i ⟶ Y) [∀ i, IsOpenImmersion (j i)]
    (hcover : ∀ y : Y, ∃ i, y ∈ (j i).opensRange)
    {M N : Y.Modules} (v w : M ⟶ N)
    (h : ∀ i, (tensorPullback (j i)).map v = (tensorPullback (j i)).map w) :
    v = w := by
  apply hom_ext
  intro V
  ext s
  have hc : V ≤ ⨆ i, V ⊓ (j i).opensRange := by
    intro y hy
    obtain ⟨i, hi⟩ := hcover y
    exact TopologicalSpace.Opens.mem_iSup.mpr ⟨i, hy, hi⟩
  apply TopCat.Sheaf.eq_of_locally_eq' ⟨N.presheaf, N.isSheaf⟩
    (fun i ↦ V ⊓ (j i).opensRange) V (fun _ ↦ homOfLE inf_le_left) hc
  intro i
  rw [← Hom.app_presheaf_map, ← Hom.app_presheaf_map]
  apply ProjectiveBundleQuotientGeometry.tensor_section_injective
    (j i) N (V ⊓ (j i).opensRange) inf_le_right
  rw [← tensor_section_map, ← tensor_section_map, h i]

-- Factorization is checked with abstract module objects, keeping geometric definitions folded.
private theorem factor_of_chart_factors {Y : Scheme.{u}} {I : Type u}
    {Z : I → Scheme.{u}} (j : ∀ i, Z i ⟶ Y) [∀ i, IsOpenImmersion (j i)]
    (hcover : ∀ y : Y, ∃ i, y ∈ (j i).opensRange)
    {M P N : Y.Modules} (q : M ⟶ P) [Epi q] (q' : M ⟶ N)
    (hlocal : ∀ i, ∃ v : (tensorPullback (j i)).obj P ⟶
      (tensorPullback (j i)).obj N,
      (tensorPullback (j i)).map q ≫ v = (tensorPullback (j i)).map q') :
    ∃ v : P ⟶ N, q ≫ v = q' := by
  have hkernel : kernel.ι q ≫ q' = 0 := by
    apply tensor_hom_ext_cover j hcover
    intro i
    obtain ⟨v, hv⟩ := hlocal i
    let : (tensorPullback (j i)).IsLeftAdjoint :=
      (tensorPullbackSectionAdjunction (j i)).isLeftAdjoint
    rw [Functor.map_comp, ← hv, ← Category.assoc, ← Functor.map_comp,
      kernel.condition, Functor.map_zero, zero_comp]
    exact (Functor.map_zero _ _ _).symm
  obtain ⟨v, hv⟩ := CokernelCofork.IsColimit.desc'
    (Abelian.epiIsCokernelOfKernel _ (kernelIsKernel q)) q' hkernel
  exact ⟨v, hv⟩

private theorem epi_comp_pullback {X Y Z : Scheme.{u}} (g : X ⟶ Y) (f : Y ⟶ Z)
    (E : Z.Modules) (N : Y.Modules) (q : (tensorPullback f).obj E ⟶ N) [Epi q] :
    Epi ((tensorPullbackSectionComp g f).hom.app E ≫ (tensorPullback g).map q) := by
  let : (tensorPullback g).IsLeftAdjoint :=
    (tensorPullbackSectionAdjunction g).isLeftAdjoint
  infer_instance

section Factorization

variable
    {X S : Scheme.{u}} (g : X ⟶ S) (E : S.Modules) [E.IsQuasicoherent]
    [((Scheme.Modules.tensorPullback g).obj E).IsQuasicoherent]
    (D : ProjectiveBundleQuotientGeometry.TautologicalQuotient E)
    (D' : ProjectiveBundleQuotientGeometry.TautologicalQuotient
      ((Scheme.Modules.tensorPullback g).obj E))
    (b : Scheme.GradedAlgebraData.PullbackData g (SymmetricAlgebraSheaf.gradedAlgebraData E)
      (SymmetricAlgebraSheaf.gradedAlgebraData ((Scheme.Modules.tensorPullback g).obj E)))
    (hb : ∀ (U : S.affineOpens) (W : X.affineOpens) (h : W.1 ≤ g ⁻¹ᵁ U.1)
      (m : E.val.obj (op U.1)),
      b.map h (SymmetricAlgebra.ι Γ(S, U.1) _ m) =
        SymmetricAlgebra.ι Γ(X, W.1) _
          (((Scheme.Modules.tensorPullback g).obj E).presheaf.map (homOfLE h).op
            (Scheme.Modules.tensorPullbackSection g E U.1 m)))
    (e : (Scheme.Modules.tensorPullback
        (b.relProjComparison ≫ (SymmetricAlgebraSheaf.gradedAlgebraData E).relProjHom)).obj E =
      (Scheme.Modules.tensorPullback
        ((SymmetricAlgebraSheaf.gradedAlgebraData
          ((Scheme.Modules.tensorPullback g).obj E)).relProjHom ≫ g)).obj E)

include hb

-- `gradedAlgebraData` stays reducible: the section binder `hb` is elaborated again here.
attribute [local irreducible] Proj

private theorem normalized_quotient_factor :
    let P := (tensorPullback b.relProjComparison).obj D.line
    let q := (tensorPullbackSectionComp b.relProjComparison
      (SymmetricAlgebraSheaf.gradedAlgebraData E).relProjHom).hom.app E ≫
      (tensorPullback b.relProjComparison).map D.quotient
    let q' := (eqToIso e).hom ≫
      (tensorPullbackSectionComp
        (SymmetricAlgebraSheaf.gradedAlgebraData
          ((tensorPullback g).obj E)).relProjHom g).hom.app E ≫
          D'.quotient
    ∃ v : P ⟶ D'.line, q ≫ v = q' := by
  classical
  intro P q q'
  let A := SymmetricAlgebraSheaf.gradedAlgebraData E
  let E' := (tensorPullback g).obj E
  let A' := SymmetricAlgebraSheaf.gradedAlgebraData E'
  let k := b.relProjComparison
  let p := A.relProjHom
  let p' := A'.relProjHom
  have hlocal (U₀ : S.affineOpens) (V : X.affineOpens) (hV : V.1 ≤ g ⁻¹ᵁ U₀.1) :
      ∃ v : (tensorPullback (A'.relProjι V)).obj P ⟶
          (tensorPullback (A'.relProjι V)).obj D'.line,
        (tensorPullback (A'.relProjι V)).map q ≫ v =
          (tensorPullback (A'.relProjι V)).map q' :=
    normalized_pullback_quotient_chart_factor g E D D' b hb e U₀ V hV
  let J := Scheme.GradedAlgebraData.PullbackData.Pairs g
  let j (a : J) := A'.relProjι a.1.1
  have hcover : ∀ y : A'.relProj, ∃ a : J, y ∈ (j a).opensRange := by
    intro y
    obtain ⟨a, ha⟩ :=
      Scheme.GradedAlgebraData.PullbackData.Pairs.exists_mem (g := g) (p' y)
    refine ⟨a, ?_⟩
    rwa [← A'.relProjHom_preimage]
  let : Epi D.quotient := D.surjective
  let : Epi q := epi_comp_pullback k p E D.line D.quotient
  exact factor_of_chart_factors j hcover q q' (fun a ↦ hlocal a.1.2 a.1.1 a.2)

end Factorization

private theorem coefficients_for_definitions {S : Scheme.{u}} (E : S.Modules)
    (T₀ : Scheme.{u}) (f : T₀ ⟶ S) (M₀ P₀ N : T₀.Modules)
    (q₀ : M₀ ⟶ P₀) (q₁ : M₀ ⟶ N)
    (s₀ : ∀ U : S.Opens, Γ(E, U) → Γ(M₀, f ⁻¹ᵁ U))
    (hf : ∃ v : P₀ ⟶ N, q₀ ≫ v = q₁) :
    let T := T₀
    let M := M₀
    let P := P₀
    let q : M ⟶ P := q₀
    let q' : M ⟶ N := q₁
    ∀ (U : S.affineOpens) (W : T.Opens) (h : W ≤ f ⁻¹ᵁ U.1)
      (x : T) (Z : T.Opens) (hZW : Z ≤ W) (_hx : x ∈ Z)
      (a : Γ(P, Z)) (c : Γ(E, U.1) → Γ(T, Z)),
      (∀ t : Γ(E, U.1),
        let s := M.presheaf.map (homOfLE (hZW.trans h)).op (s₀ U.1 t)
        q.app Z s = c t • a) →
      ∃ b' : Γ(N, Z), ∀ t : Γ(E, U.1),
        let s := M.presheaf.map (homOfLE (hZW.trans h)).op (s₀ U.1 t)
        q'.app Z s = c t • b' := by
  intro T M P q q' U W h x Z hZW _hx a c hc
  obtain ⟨v, hv⟩ := hf
  have hv' : q ≫ v = q' := hv
  refine ⟨v.app Z a, ?_⟩
  intro t s
  rw [← hv', Hom.comp_app]
  change v.app Z (q.app Z s) = _
  rw [hc t, Hom.app_smul]

-- Keep the existing public binders, including the point-membership witness.
set_option linter.unusedVariables false in
/-- The matching local frame for the normalized second quotient map.

The open, the first frame, and its coefficient map are fixed as input. The
conclusion is only the existence of the second frame and its formula, hence is
strictly smaller than the common-coefficient theorem.

Source: Stacks Project, Constructions, Tags 01N2, 01NQ, 01NR and 01OB.
Proof: on standard degree-one charts the normalization of both quotients identifies
images of generators with their homogeneous fractions. The map `b` sends these
fractions to the fractions for the pulled generators, by `hb`. Hence the two
normalized quotients have the same kernel on the pulled generators. Such generators
span the pullback of `E` locally, because `U` is affine and `E` is quasi-coherent.
The first quotient is surjective, so the equation `q(t) = c(t) • a` implies that
`a` generates its invertible target at every stalk. Thus `a` is a frame on `Z`.
Expressing the second normalized quotient in that frame yields a section `b'`;
the common-kernel equation proves `q'(t) = c(t) • b'` on a standard-open cover.
The local sections `b'` agree on intersections by the generating property of the
coefficients `c(t)`, and glue to the required section on `Z`. The zero-ring and
empty-open cases satisfy the same formulas. This argument requires the specified
normalized `q'`; it does not apply to an arbitrary morphism.
(blueprint: lem-trf-symmetric-proj-pullback-generator-local-coefficients-qprime)
-/
theorem normalized_pullback_generator_local_coefficients_qprime
    {X S : Scheme.{u}} (g : X ⟶ S) (E : S.Modules) [E.IsQuasicoherent]
    [((Scheme.Modules.tensorPullback g).obj E).IsQuasicoherent]
    (D : ProjectiveBundleQuotientGeometry.TautologicalQuotient E)
    (D' : ProjectiveBundleQuotientGeometry.TautologicalQuotient
      ((Scheme.Modules.tensorPullback g).obj E))
    (b : Scheme.GradedAlgebraData.PullbackData g (SymmetricAlgebraSheaf.gradedAlgebraData E)
      (SymmetricAlgebraSheaf.gradedAlgebraData ((Scheme.Modules.tensorPullback g).obj E)))
    (hb : ∀ (U : S.affineOpens) (W : X.affineOpens) (h : W.1 ≤ g ⁻¹ᵁ U.1)
      (m : E.val.obj (op U.1)),
      b.map h (SymmetricAlgebra.ι Γ(S, U.1) _ m) =
        SymmetricAlgebra.ι Γ(X, W.1) _
          (((Scheme.Modules.tensorPullback g).obj E).presheaf.map (homOfLE h).op
            (Scheme.Modules.tensorPullbackSection g E U.1 m)))
    (e : (Scheme.Modules.tensorPullback
        (b.relProjComparison ≫ (SymmetricAlgebraSheaf.gradedAlgebraData E).relProjHom)).obj E =
      (Scheme.Modules.tensorPullback
        ((SymmetricAlgebraSheaf.gradedAlgebraData
          ((Scheme.Modules.tensorPullback g).obj E)).relProjHom ≫ g)).obj E) :
    let T := (SymmetricAlgebraSheaf.gradedAlgebraData
      ((Scheme.Modules.tensorPullback g).obj E)).relProj
    let M := (Scheme.Modules.tensorPullback
      (b.relProjComparison ≫ (SymmetricAlgebraSheaf.gradedAlgebraData E).relProjHom)).obj E
    let P := (Scheme.Modules.tensorPullback b.relProjComparison).obj D.line
    let q : M ⟶ P :=
      (Scheme.Modules.tensorPullbackSectionComp b.relProjComparison
        (SymmetricAlgebraSheaf.gradedAlgebraData E).relProjHom).hom.app E ≫
        (Scheme.Modules.tensorPullback b.relProjComparison).map D.quotient
    let q' : M ⟶ D'.line := (eqToIso e).hom ≫
      (Scheme.Modules.tensorPullbackSectionComp
        (SymmetricAlgebraSheaf.gradedAlgebraData
          ((Scheme.Modules.tensorPullback g).obj E)).relProjHom g).hom.app E ≫ D'.quotient
    ∀ (U : S.affineOpens) (W : T.Opens) (h : W ≤
      (b.relProjComparison ≫ (SymmetricAlgebraSheaf.gradedAlgebraData E).relProjHom) ⁻¹ᵁ U.1)
      (x : T) (Z : T.Opens) (hZW : Z ≤ W) (hx : x ∈ Z)
      (a : Γ(P, Z)) (c : Γ(E, U.1) → Γ(T, Z)),
      (∀ t : Γ(E, U.1),
        let s := M.presheaf.map (homOfLE (hZW.trans h)).op
          (Scheme.Modules.tensorPullbackSection
            (b.relProjComparison ≫ (SymmetricAlgebraSheaf.gradedAlgebraData E).relProjHom)
            E U.1 t)
        q.app Z s = c t • a) →
      ∃ (b' : Γ(D'.line, Z)),
        ∀ t : Γ(E, U.1),
          let s := M.presheaf.map (homOfLE (hZW.trans h)).op
            (Scheme.Modules.tensorPullbackSection
              (b.relProjComparison ≫ (SymmetricAlgebraSheaf.gradedAlgebraData E).relProjHom)
              E U.1 t)
          q'.app Z s = c t • b' := by
  exact coefficients_for_definitions E
    (SymmetricAlgebraSheaf.gradedAlgebraData ((tensorPullback g).obj E)).relProj
    (b.relProjComparison ≫ (SymmetricAlgebraSheaf.gradedAlgebraData E).relProjHom)
    ((tensorPullback (b.relProjComparison ≫
      (SymmetricAlgebraSheaf.gradedAlgebraData E).relProjHom)).obj E)
    ((tensorPullback b.relProjComparison).obj D.line) D'.line
    ((tensorPullbackSectionComp b.relProjComparison
      (SymmetricAlgebraSheaf.gradedAlgebraData E).relProjHom).hom.app E ≫
        (tensorPullback b.relProjComparison).map D.quotient)
    ((eqToIso e).hom ≫ (tensorPullbackSectionComp
      (SymmetricAlgebraSheaf.gradedAlgebraData ((tensorPullback g).obj E)).relProjHom
      g).hom.app E ≫ D'.quotient)
    (tensorPullbackSection
      (b.relProjComparison ≫ (SymmetricAlgebraSheaf.gradedAlgebraData E).relProjHom) E)
    (normalized_quotient_factor g E D D' b hb e)

end AlgebraicGeometry.SymmetricProjTautologicalCharts
