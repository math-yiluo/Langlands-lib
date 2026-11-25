/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.ProjectiveBundleQuotientGeometry.ProjectiveBundleQuotientData
public import WeilConjectures.AlgebraicGeometry.RelativeProj.BaseChange
public import WeilConjectures.AlgebraicGeometry.Modules.TensorSection
import WeilConjectures.AlgebraicGeometry.SymmetricProjTautologicalCharts.SymmetricProjPullbackGeneratorCrossTensor
import WeilConjectures.AlgebraicGeometry.ModulePullbackAffineSections

/-! # Degree-two relation for the normalized pullback quotients

Source: Stacks Project, Constructions, Tags 01N2, 01NQ, 01NR and 01OB.
(blueprint: lem-trf-symmetric-proj-pullback-quotient-cross-tensor).
-/

@[expose] public section

set_option autoImplicit false
set_option relaxedAutoImplicit false

universe u
open CategoryTheory Opposite
open scoped AlgebraicGeometry

namespace AlgebraicGeometry.SymmetricProjTautologicalCharts

attribute [local instance 2000] CategoryTheory.Abelian.hasFiniteLimits

attribute [local irreducible] Scheme.Modules.tensorPullback Scheme.Modules.tensorPullbackObj
  Scheme.Modules.tensorPullbackSectionComp Scheme.Modules.tensorPullbackSectionAdjunction
  Scheme.GradedAlgebraData.relProj Scheme.GradedAlgebraData.relProjι
  Scheme.GradedAlgebraData.PullbackData.relProjComparison

open Scheme.Modules CategoryTheory.MonoidalCategory

private theorem cross_tensor_affine {S T : Scheme.{u}} (h : T ⟶ S)
    (E : S.Modules) [E.IsQuasicoherent] {P Q : T.Modules}
    (q : (tensorPullback h).obj E ⟶ P) (q' : (tensorPullback h).obj E ⟶ Q)
    (U : S.affineOpens) (W : T.affineOpens) (hWU : W.1 ≤ h ⁻¹ᵁ U.1)
    (hpure : ∀ m n : Γ(E, U.1),
      let m' := ((tensorPullback h).obj E).presheaf.map (homOfLE hWU).op
        (tensorPullbackSection h E U.1 m)
      let n' := ((tensorPullback h).obj E).presheaf.map (homOfLE hWU).op
        (tensorPullbackSection h E U.1 n)
      tmulSection (q.app W.1 m') (q'.app W.1 n') =
        tmulSection (q.app W.1 n') (q'.app W.1 m')) :
    ∀ m n : Γ((tensorPullback h).obj E, W.1),
      tmulSection (q.app W.1 m) (q'.app W.1 n) =
        tmulSection (q.app W.1 n) (q'.app W.1 m) := by
  classical
  let : Algebra Γ(S, U.1) Γ(T, W.1) := (h.appLE U.1 W.1 hWU).hom.toAlgebra
  let : ∀ G : S.Modules, Module Γ(S, U.1) Γ((tensorPullback h).obj G, W.1) :=
    fun G ↦ Module.compHom _ (h.appLE U.1 W.1 hWU).hom
  obtain ⟨c, hc, _, hp, _⟩ := exists_tensorPullback_affine_sections h U W hWU
  have hunit (m : Γ(E, U.1)) :
      (((Classical.choose (exists_tensorPullbackAdjunction h)).unit.app E).val.app
        (op U.1) m) = tensorPullbackSection h E U.1 m := by
    unfold tensorPullbackSection
    exact Classical.choose_spec (exists_tensorPullbackAdjunction h) E (op U.1) m
  intro m n
  obtain ⟨a, rfl⟩ := (hc E inferInstance).surjective m
  obtain ⟨b, rfl⟩ := (hc E inferInstance).surjective n
  induction a using TensorProduct.inductionOn with
  | tmul m r =>
    induction b using TensorProduct.inductionOn with
    | tmul n s =>
      simp only [hp, hunit, Hom.app_smul, smul_tmulSection, tmulSection_smul]
      rw [hpure]
      apply smul_comm
    | add b b' hb hb' =>
      simp only [map_add, tmulSection_add, add_tmulSection, hb, hb']
  | add a a' ha ha' =>
    simp only [map_add, tmulSection_add, add_tmulSection, ha, ha']

private theorem cross_tensor_of_pulled_generators {S T : Scheme.{u}} (h : T ⟶ S)
    (E : S.Modules) [E.IsQuasicoherent] {P Q : T.Modules}
    (q : (tensorPullback h).obj E ⟶ P) (q' : (tensorPullback h).obj E ⟶ Q)
    (hpure : ∀ (U : S.affineOpens) (W : T.affineOpens) (hWU : W.1 ≤ h ⁻¹ᵁ U.1)
      (m n : Γ(E, U.1)),
      let m' := ((tensorPullback h).obj E).presheaf.map (homOfLE hWU).op
        (tensorPullbackSection h E U.1 m)
      let n' := ((tensorPullback h).obj E).presheaf.map (homOfLE hWU).op
        (tensorPullbackSection h E U.1 n)
      tmulSection (q.app W.1 m') (q'.app W.1 n') =
        tmulSection (q.app W.1 n') (q'.app W.1 m')) :
    ∀ (V : T.Opens) (m n : Γ((tensorPullback h).obj E, V)),
      tmulSection (q.app V m) (q'.app V n) =
        tmulSection (q.app V n) (q'.app V m) := by
  intro V m n
  apply (P ⊗ Q).isSheaf.section_ext
  intro x hx
  obtain ⟨U₀, hU₀, hxU, _⟩ := exists_isAffineOpen_mem_and_subset
    (x := h x) (U := ⊤) trivial
  let U : S.affineOpens := ⟨U₀, hU₀⟩
  obtain ⟨W, hW, hxW, hWV⟩ := exists_isAffineOpen_mem_and_subset
    (x := x) (U := V ⊓ h ⁻¹ᵁ U.1) ⟨hx, hxU⟩
  refine ⟨W, hWV.trans inf_le_left, hxW, ?_⟩
  rw [tmulSection_map, tmulSection_map, ← Hom.app_presheaf_map,
    ← Hom.app_presheaf_map, ← Hom.app_presheaf_map, ← Hom.app_presheaf_map]
  exact cross_tensor_affine h E q q' U ⟨W, hW⟩ (hWV.trans inf_le_right)
    (hpure U ⟨W, hW⟩ (hWV.trans inf_le_right)) _ _

/-- The two normalized quotients satisfy the degree-two cross relation.

Source: Stacks Project, Constructions, Tag 01N2 (lemma-base-change-map-proj),
Tag 01NQ (lemma-relative-proj-base-change), Tag 01NR (lemma-glue-relative-proj-twists),
and Tag 01OB (definition-projective-bundle).
(blueprint: lem-trf-symmetric-proj-pullback-quotient-cross-tensor).

Proof: work over affine pairs W contained in g inverse U, then on the standard
opens D_+(b(iota(v))) of Proj Sym(g*E)(W). These opens cover: scalar extension
identifies degree one with the span of the images of E(U), and a homogeneous
prime containing their images would contain the irrelevant ideal. In the twist
charts of D and D', the images of pulled generators m and n are respectively
iota(m) and iota(n) in the old twist, and b(iota(m)) and b(iota(n)) in the new
twist. Divide by the respective degree-one frame. The old coefficients pull back
to b(iota(m))/b(iota(v)) and b(iota(n))/b(iota(v)), which are also the new
coefficients by hb. Thus the two cross tensors have equal coefficients, by
commutativity of the localized ring. This calculation asserts only equality of
tensor sections, and requires no choice or gluing of a line isomorphism.
The affine tensor-pullback section comparison expresses all local sections as
finite sums of scalar multiples of pulled generators. Bilinearity extends the
cross relation to those sums. The normalized pullback composition identifies the
maps in this calculation with q and q'; proof irrelevance removes dependence on
the proof e. Refine affine-base overlaps by affine opens and use separatedness of
the tensor sheaf to obtain equality on every open V. Empty standard opens and
zero rings give the same equality; no finite generation or flatness is used. -/
theorem normalized_pullback_cross_tensor
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
    ∀ (V : T.Opens) (m n : Γ(M, V)),
      Scheme.Modules.tmulSection (q.app V m) (q'.app V n) =
        Scheme.Modules.tmulSection (q.app V n) (q'.app V m) := by
  exact cross_tensor_of_pulled_generators _ E _ _
    (normalized_pullback_generator_cross_tensor g E D D' b hb e)

end AlgebraicGeometry.SymmetricProjTautologicalCharts
