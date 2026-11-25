/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.GradedSheafStructures
public import WeilConjectures.AlgebraicGeometry.QuasiCoherentAlgebra
public import Mathlib.AlgebraicGeometry.ProjectiveSpectrum.Functor
public import Mathlib.AlgebraicGeometry.RelativeGluing
public import Mathlib.AlgebraicGeometry.Cover.Directed
import WeilConjectures.AlgebraicGeometry.QuasiCoherentAffineSectionBaseChange
import WeilConjectures.Mathlib.Algebra.Category.ModuleCat.Presheaf.Sheafification
import WeilConjectures.Mathlib.Algebra.Category.Grp.Colimits
import Mathlib.Topology.Sheaves.LocallySurjective
import Mathlib.Algebra.Category.Grp.EpiMono
import Mathlib.CategoryTheory.Sites.Abelian

/-! # Relative Proj construction data

The input records the underlying quasi-coherent algebra and its homogeneous sheaves,
with the direct-sum identification and its multiplication and unit equations. On affine
opens the sections of this sum are the sum of sections. The local schemes are ordinary
Proj schemes. Relative gluing over the basis of all affine opens records overlaps by
pullback squares; intersections need not be affine. The output includes every affine
restriction identification. No existence of the output is asserted here.

## References

* Stacks Project, Constructions, Tag 01LH
-/

@[expose] public section

universe u

open CategoryTheory CategoryTheory.Limits Opposite
open scoped TensorProduct DirectSum
open TopologicalSpace

noncomputable section

namespace AlgebraicGeometry

/-- A quasi-coherent commutative graded algebra sheaf, including the identification of
its underlying module with the sheaf direct sum of its homogeneous pieces.
The last two equations say that this identification respects the given graded algebra. -/
structure RelativeProjAlgebra (X : Scheme.{u}) where
  algebra : QuasiCoherentAlgebra X
  piece : ℕ → X.Modules
  graded : GradedSheafAlgebra piece
  decomposition : (∐ piece) ≅ algebra.obj.toModule
  mul_eq : ∀ (U : X.Opens) (m n : ℕ)
    (a : (piece m).val.obj (op U)) (b : (piece n).val.obj (op U)),
    ((Sigma.ι piece (m + n) ≫ decomposition.hom).val.app (op U))
        (graded.mul m n U a b) =
      (@id (algebra.obj.right.obj.obj (op U))
        (((Sigma.ι piece m ≫ decomposition.hom).val.app (op U)) a)) *
        (@id (algebra.obj.right.obj.obj (op U))
          (((Sigma.ι piece n ≫ decomposition.hom).val.app (op U)) b))
  unit_eq : ∀ (U : X.Opens) (r : Γ(X, U)),
    ((Sigma.ι piece 0 ≫ decomposition.hom).val.app (op U))
        (graded.unit.val.app (op U) r) = algebra.obj.hom.hom.app (op U) r

namespace RelativeProjAlgebra

variable {X : Scheme.{u}} (A : RelativeProjAlgebra X)

/-- The actual section ring of the input algebra on an affine open, not a chosen model. -/
abbrev sections (V : X.affineOpens) : CommRingCat.{u} :=
  A.algebra.obj.right.obj.obj (op V.1)

/-- The homogeneous section subgroup is the image of the homogeneous-sheaf inclusion. -/
def sectionGrade (V : X.affineOpens) (n : ℕ) : AddSubgroup (A.sections V) :=
  (((Sigma.ι A.piece n ≫ A.decomposition.hom).val.app (op V.1)).hom.toAddMonoidHom).range

/-- The degree-zero unit belongs to the degree-zero subgroup. -/
theorem sectionGrade_one (V : X.affineOpens) : 1 ∈ A.sectionGrade V 0 := by
  refine ⟨A.graded.unit.val.app (op V.1) (1 : Γ(X, V.1)), ?_⟩
  simpa using A.unit_eq V.1 1

/-- Homogeneous multiplication adds degrees. -/
theorem sectionGrade_mul (V : X.affineOpens) (m n : ℕ)
    (a b : A.sections V) (ha : a ∈ A.sectionGrade V m) (hb : b ∈ A.sectionGrade V n) :
    a * b ∈ A.sectionGrade V (m + n) := by
  obtain ⟨a, rfl⟩ := ha
  obtain ⟨b, rfl⟩ := hb
  exact ⟨A.graded.mul m n V.1 a b, A.mul_eq V.1 m n a b⟩

private def homogeneousProjection (n : ℕ) :
    (A.algebra.obj.toModule : X.Modules) ⟶ (A.algebra.obj.toModule : X.Modules) :=
  A.decomposition.inv ≫ Sigma.π A.piece n ≫ Sigma.ι A.piece n ≫ A.decomposition.hom

private theorem homogeneousProjection_mem (n : ℕ) (V : X.affineOpens) (a : A.sections V) :
    (Scheme.Modules.Hom.app (X := X) (homogeneousProjection A n)) V.1 a ∈ A.sectionGrade V n := by
  exact ⟨(A.decomposition.inv ≫ Sigma.π A.piece n).app V.1 a, rfl⟩

private theorem homogeneousProjection_eq (n : ℕ) (V : X.affineOpens) (a : A.sections V)
    (ha : a ∈ A.sectionGrade V n) : (Scheme.Modules.Hom.app (X := X) (homogeneousProjection A n))
      V.1 a = a := by
  obtain ⟨a, rfl⟩ := ha
  have hp : (Sigma.ι A.piece n ≫ A.decomposition.hom) ≫ homogeneousProjection A n =
      Sigma.ι A.piece n ≫ A.decomposition.hom := by
    simp [homogeneousProjection]
  exact congrArg (fun f ↦ f.app V.1 a) hp

private theorem inclusion_homogeneousProjection (i j : ℕ) :
    (Sigma.ι A.piece i ≫ A.decomposition.hom) ≫ homogeneousProjection A j =
      if i = j then Sigma.ι A.piece i ≫ A.decomposition.hom else 0 := by
  by_cases h : i = j
  · subst j
    simp [homogeneousProjection]
  · simp [homogeneousProjection, h, Sigma.ι_π_of_ne_assoc _ h]

private theorem projection_inclusion_apply (U : X.Opens) (i j : ℕ)
    (a : Γ(A.piece i, U)) :
    (Scheme.Modules.Hom.app (X := X) (homogeneousProjection A j)) U ((Sigma.ι A.piece i ≫
      A.decomposition.hom).app U a) =
      if i = j then (Sigma.ι A.piece i ≫ A.decomposition.hom).app U a else 0 := by
  have h := congrArg (fun f ↦ f.app U a) (inclusion_homogeneousProjection A i j)
  split_ifs at h ⊢ <;> exact h

private theorem locally_finite_sections (U : X.Opens) (s : Γ(A.algebra.obj.toModule, U))
    (x : X) (hx : x ∈ U) :
    ∃ (W : X.Opens) (hWU : W ≤ U), x ∈ W ∧
      ∃ (T : Finset ℕ) (a : ∀ i, Γ(A.piece i, W)),
        (Scheme.Modules.presheaf (X := X) A.algebra.obj.toModule).map (homOfLE hWU).op s =
          ∑ i ∈ T, (Sigma.ι A.piece i ≫ A.decomposition.hom).app W (a i) := by
  classical
  let J := _root_.Opens.grothendieckTopology X
  let H := SheafOfModules.toSheaf X.ringCatSheaf
  let F := fun i ↦ H.obj (A.piece i)
  let G := H.obj A.algebra.obj.toModule
  let c : Cofan F := Cofan.mk G (fun i ↦ H.map (Sigma.ι A.piece i ≫ A.decomposition.hom))
  have hc : IsColimit c := by
    have hc₀ := isColimitCofanMkObjOfIsColimit H _ (Sigma.ι A.piece)
      (coproductIsCoproduct A.piece)
    refine IsColimit.ofIsoColimit hc₀ (Cofan.ext (H.mapIso A.decomposition) ?_)
    intro i
    simp [c, Functor.map_comp]
  let P := ∐ fun i ↦ (F i).obj
  let φ : P ⟶ G.obj := Sigma.desc fun i ↦ (c.inj i).hom
  let ψ : (presheafToSheaf J AddCommGrpCat.{u}).obj P ⟶ G :=
    ⟨sheafifyLift J φ G.property⟩
  have hφ : φ = toSheafify J P ≫ ψ.hom := (toSheafify_sheafifyLift _ _ _).symm
  have hψ : Epi ψ := by
    refine ⟨fun {Z} g h hgh ↦ Cofan.IsColimit.hom_ext hc _ _ fun i ↦ ?_⟩
    have e : c.inj i = (⟨Sigma.ι (fun i ↦ (F i).obj) i ≫ toSheafify J P⟩ :
        F i ⟶ (presheafToSheaf J AddCommGrpCat.{u}).obj P) ≫ ψ := by
      ext1
      change _ = Sigma.ι (fun i ↦ (F i).obj) i ≫ toSheafify J P ≫ ψ.hom
      rw [← hφ, Sigma.ι_comp_desc]
    rw [e, Category.assoc, Category.assoc, hgh]
  have := (Sheaf.isLocallySurjective_iff_epi' (A := AddCommGrpCat.{u}) ψ).2 hψ
  have hsurj : Presheaf.IsLocallySurjective J φ := by
    rw [hφ]
    infer_instance
  obtain ⟨W, hWU, ⟨p, hp⟩, hxW⟩ :=
    (TopCat.Presheaf.isLocallySurjective_iff φ).mp hsurj U s x hx
  have hP := isColimitCofanMkObjOfIsColimit ((CategoryTheory.evaluation _ _).obj (op W)) _
    (Sigma.ι fun i ↦ (F i).obj) (coproductIsCoproduct _)
  obtain ⟨T, a, rfl⟩ := AddCommGrpCat.exists_eq_sum_of_isColimit_cofan hP p
  refine ⟨W, hWU, hxW, T, a, hp.symm.trans ?_⟩
  rw [map_sum]
  refine Finset.sum_congr rfl fun i _ ↦ ?_
  change (Sigma.ι (fun i ↦ (F i).obj) i ≫ φ).app (op W) (a i) = _
  rw [Sigma.ι_comp_desc]
  rfl

private theorem finite_sections_of_local_presentations
    (F : ℕ → Sheaf (_root_.Opens.grothendieckTopology X) AddCommGrpCat.{u})
    (G : Sheaf (_root_.Opens.grothendieckTopology X) AddCommGrpCat.{u})
    (inc : ∀ i, F i ⟶ G) (p : ℕ → (G ⟶ G))
    (hp : ∀ (U : X.Opens) (i j : ℕ) (a : (F i).obj.obj (op U)),
      (p j).hom.app (op U) ((inc i).hom.app (op U) a) =
        if i = j then (inc i).hom.app (op U) a else 0)
    (hloc : ∀ (U : X.Opens) (s : G.obj.obj (op U)) (x : X), x ∈ U →
      ∃ (W : X.Opens) (hWU : W ≤ U), x ∈ W ∧
        ∃ (T : Finset ℕ) (a : ∀ i, (F i).obj.obj (op W)),
          G.obj.map (homOfLE hWU).op s = ∑ i ∈ T, (inc i).hom.app (op W) (a i))
    (U : X.Opens) (hU : IsCompact (U : Set X)) (s : G.obj.obj (op U)) :
    ∃ S : Finset ℕ, s = ∑ i ∈ S, (p i).hom.app (op U) s := by
  classical
  choose W hW hxW T a he using fun x : U ↦ hloc U s x.1 x.2
  have hcov : (U : Set X) ⊆ ⋃ x : U, (W x : Set X) := by
    intro x hx
    exact Set.mem_iUnion.mpr ⟨⟨x, hx⟩, hxW ⟨x, hx⟩⟩
  obtain ⟨K, hK⟩ := hU.elim_finite_subcover
    (fun x : U ↦ (W x : Set X)) (fun x ↦ (W x).isOpen) hcov
  let S := K.biUnion T
  refine ⟨S, ?_⟩
  have hsheaf : TopCat.Presheaf.IsSheaf (X := TopCat.of X) G.obj := G.property
  apply hsheaf.section_ext
  intro x hx
  obtain ⟨y, hy⟩ := Set.mem_iUnion.mp (hK hx)
  obtain ⟨hyK, hxy⟩ := Set.mem_iUnion.mp hy
  refine ⟨W y, hW y, hxy, ?_⟩
  have hnat (i : ℕ) :
      G.obj.map (homOfLE (hW y)).op ((p i).hom.app (op U) s) =
        (p i).hom.app (op (W y)) (G.obj.map (homOfLE (hW y)).op s) := by
    exact (congrArg (fun f ↦ f s) ((p i).hom.naturality (homOfLE (hW y)).op)).symm
  rw [map_sum]
  simp_rw [hnat, he y, map_sum]
  rw [Finset.sum_comm]
  symm
  apply Finset.sum_congr rfl
  intro i hi
  simp only [hp]
  have hiS : i ∈ S := Finset.mem_biUnion.mpr ⟨y, hyK, hi⟩
  simp [hiS]

private theorem finite_sections (V : X.affineOpens) (s : A.sections V) :
    ∃ S : Finset ℕ, s = ∑ i ∈ S, (Scheme.Modules.Hom.app (X := X)
      (homogeneousProjection A i)) V.1 s := by
  let H := SheafOfModules.toSheaf X.ringCatSheaf
  exact finite_sections_of_local_presentations
    (fun i ↦ H.obj (A.piece i)) (H.obj A.algebra.obj.toModule)
    (fun i ↦ H.map (Sigma.ι A.piece i ≫ A.decomposition.hom))
    (fun i ↦ H.map (homogeneousProjection A i)) (projection_inclusion_apply A)
    (locally_finite_sections A) V.1 V.2.isCompact s

/-- On an affine open the homogeneous section subgroups are an internal direct sum. -/
theorem sectionGrade_internal (V : X.affineOpens) :
    DirectSum.IsInternal (A.sectionGrade V) := by
  classical
  let f := DirectSum.coeAddMonoidHom (A.sectionGrade V)
  have hp (n : ℕ) (t : ⨁ i, A.sectionGrade V i) :
      (Scheme.Modules.Hom.app (X := X) (homogeneousProjection A n)) V.1 (f t) = (t n : A.sections
        V) := by
    induction t using DirectSum.induction_on with
    | zero => simp [f]
    | of i a =>
        rw [DirectSum.coeAddMonoidHom_of, DirectSum.coe_of_apply]
        split_ifs with h
        · subst n
          exact homogeneousProjection_eq A i V a a.property
        · obtain ⟨b, hb⟩ := a.property
          rw [← hb]
          change (Scheme.Modules.Hom.app (X := X) (homogeneousProjection A n)) V.1
            ((Sigma.ι A.piece i ≫ A.decomposition.hom).app V.1 b) = 0
          simpa only [ite_eq_right h] using projection_inclusion_apply A V.1 i n b
    | add t s ht hs =>
        simp only [map_add, ht, hs, DirectSum.add_apply]
        rfl
  refine ⟨?_, ?_⟩
  · intro t s hts
    apply DirectSum.ext
    intro n
    apply Subtype.ext
    rw [← hp n t, ← hp n s, hts]
  · intro s
    obtain ⟨S, hS⟩ := finite_sections A V s
    refine ⟨∑ i ∈ S, DirectSum.of (fun i ↦ A.sectionGrade V i) i
      ⟨(Scheme.Modules.Hom.app (X := X) (homogeneousProjection A i)) V.1 s,
        homogeneousProjection_mem A i V s⟩, ?_⟩
    simpa only [map_sum, DirectSum.coeAddMonoidHom_of] using hS.symm

/-- The induced grading on the section ring. The decomposition is the unique inverse of
the bijective recomposition map, not data selected from an unrestricted existence claim. -/
noncomputable instance sectionGradedRing (V : X.affineOpens) :
    GradedRing (A.sectionGrade V) where
  toDecomposition := (A.sectionGrade_internal V).chooseDecomposition
  one_mem := A.sectionGrade_one V
  mul_mem := A.sectionGrade_mul V

/-- Restriction of the algebra sheaf preserves every homogeneous subgroup. -/
theorem restriction_mem {V W : X.affineOpens} (h : W ≤ V) (n : ℕ)
    (a : A.sections V) (ha : a ∈ A.sectionGrade V n) :
    (A.algebra.obj.right.obj.map (homOfLE h).op).hom a ∈ A.sectionGrade W n := by
  obtain ⟨a, rfl⟩ := ha
  refine ⟨(A.piece n).val.map (homOfLE (X := X.Opens) h).op a, ?_⟩
  exact congrArg (fun f ↦ f a)
    ((Sigma.ι A.piece n ≫ A.decomposition.hom).val.naturality (homOfLE (X := X.Opens) h).op)

/-- The graded section restriction homomorphism. -/
def restriction {V W : X.affineOpens} (h : W ≤ V) :
    A.sectionGrade V →+*ᵍ A.sectionGrade W where
  toRingHom := (A.algebra.obj.right.obj.map (homOfLE h).op).hom
  map_mem := fun {n} {a} ha ↦ A.restriction_mem h n a ha

/-- Affine restriction extends the irrelevant ideal to the irrelevant ideal. -/
theorem irrelevant_le {V W : X.affineOpens} (h : W ≤ V) :
    HomogeneousIdeal.irrelevant (A.sectionGrade W) ≤
      (HomogeneousIdeal.irrelevant (A.sectionGrade V)).map (A.restriction h) := by
  classical
  apply (HomogeneousIdeal.irrelevant_le _).mpr
  intro n hn b hb
  let F : X.Modules := A.algebra.obj.toModule
  let : F.IsQuasicoherent := A.algebra.property
  let : Algebra Γ(X, V.1) Γ(X, W.1) :=
    (X.presheaf.map (homOfLE (X := X.Opens) h).op).hom.toAlgebra
  let : Module Γ(X, V.1) Γ(F, W.1) :=
    Module.compHom _ (X.presheaf.map (homOfLE (X := X.Opens) h).op).hom
  obtain ⟨c, hc, _, ht⟩ :=
    Scheme.Modules.quasiCoherent_affine_section_baseChange X F W V h
  let I := (HomogeneousIdeal.irrelevant (A.sectionGrade V)).map (A.restriction h)
  have hm (t : Γ(F, V.1) ⊗[Γ(X, V.1)] Γ(X, W.1)) :
      (Scheme.Modules.Hom.app (X := X) (homogeneousProjection A n)) W.1 (c t) ∈ I := by
    induction t using TensorProduct.inductionOn with
    | tmul a r =>
        rw [ht, Scheme.Modules.Hom.app_smul]
        have he : (Scheme.Modules.Hom.app (X := X) (homogeneousProjection A n)) W.1
            (F.presheaf.map (homOfLE (X := X.Opens) h).op a) =
            F.presheaf.map (homOfLE (X := X.Opens) h).op
              ((Scheme.Modules.Hom.app (X := X) (homogeneousProjection A n)) V.1 a) := by
          exact (congrArg (fun f ↦ f a)
            ((homogeneousProjection A n).val.naturality (homOfLE (X := X.Opens) h).op))
        rw [he]
        change (A.algebra.obj.hom.hom.app (op W.1)).hom r *
          A.restriction h ((Scheme.Modules.Hom.app (X := X) (homogeneousProjection A n)) V.1 a) ∈
            I.toIdeal
        exact I.toIdeal.mul_mem_left _ (Ideal.mem_map_of_mem (A.restriction h)
          (HomogeneousIdeal.mem_irrelevant_of_mem _ hn (homogeneousProjection_mem A n V a)))
    | add t s ht hs => simpa using I.toIdeal.add_mem ht hs
  obtain ⟨t, htb⟩ := hc.2 b
  change b ∈ I
  simpa only [htb, homogeneousProjection_eq A n W b hb] using hm t

/-- The structural unit of the section algebra has degree zero. -/
theorem unit_mem (V : X.affineOpens) (r : Γ(X, V.1)) :
    (A.algebra.obj.hom.hom.app (op V.1)).hom r ∈ A.sectionGrade V 0 := by
  exact ⟨A.graded.unit.val.app (op V.1) r, A.unit_eq V.1 r⟩

/-- The base-ring homomorphism into degree zero; it need not be an isomorphism. -/
def unitZero (V : X.affineOpens) : Γ(X, V.1) →+* A.sectionGrade V 0 where
  toFun r := ⟨(A.algebra.obj.hom.hom.app (op V.1)).hom r, A.unit_mem V r⟩
  map_zero' := Subtype.ext (map_zero _)
  map_one' := Subtype.ext (map_one _)
  map_add' r s := Subtype.ext (map_add _ r s)
  map_mul' r s := Subtype.ext (map_mul _ r s)

/-- The local model on an affine open is Proj of its graded section ring. -/
def localProj (V : X.affineOpens) : Scheme.{u} := Proj (A.sectionGrade V)

/-- The local structural map is the degree-zero Proj map followed by the spectrum map
of the unit into degree zero and the canonical affine identification. -/
def localBase (V : X.affineOpens) : A.localProj V ⟶ V.1.toScheme :=
  Proj.toSpecZero (A.sectionGrade V) ≫ Spec.map (CommRingCat.ofHom (A.unitZero V)) ≫
    V.2.isoSpec.inv

/-- The local transition is precisely the Proj map of section restriction. Its standard
chart maps are the degree-zero homogeneous localization maps in Mathlib's `Proj.map`. -/
def localTransition {V W : X.affineOpens} (h : W ≤ V) :
    A.localProj W ⟶ A.localProj V :=
  Proj.map (A.restriction h) (A.irrelevant_le h)

end RelativeProjAlgebra

/-- Relative Proj construction datum over the cover by all affine opens: relative gluing data
(`gluing`, with glued scheme `gluing.glued` over `gluing.toBase`), local Proj models with
their structure maps and overlap transitions, and the affine restriction identifications
`restrictionIso` with their compatibilities. -/
structure RelativeProjData {X : Scheme.{u}} (A : RelativeProjAlgebra X) where
  gluing : Scheme.Cover.RelativeGluingData X.directedAffineCover
  localIso : ∀ V : X.affineOpens, gluing.functor.obj V ≅ A.localProj V
  local_over : ∀ V : X.affineOpens,
    (localIso V).hom ≫ A.localBase V = gluing.natTrans.app V
  local_transition : ∀ (V W : X.affineOpens) (h : W ≤ V),
    gluing.functor.map (homOfLE h) ≫ (localIso V).hom =
      (localIso W).hom ≫ A.localTransition h
  restrictionIso : ∀ V : X.affineOpens,
    (gluing.toBase ⁻¹ᵁ V.1).toScheme ≅ A.localProj V
  restriction_ι : ∀ V : X.affineOpens,
    (restrictionIso V).hom ≫ (localIso V).inv ≫ colimit.ι gluing.functor V =
      (gluing.toBase ⁻¹ᵁ V.1).ι
  restriction_over : ∀ V : X.affineOpens,
    (restrictionIso V).hom ≫ A.localBase V ≫ V.1.ι =
      (gluing.toBase ⁻¹ᵁ V.1).ι ≫ gluing.toBase
  restriction_compatibility : ∀ (V W : X.affineOpens) (h : W ≤ V),
    (restrictionIso W).inv ≫
        gluing.glued.homOfLE (gluing.toBase.preimage_mono h) ≫
          (restrictionIso V).hom = A.localTransition h

namespace RelativeProjData

variable {X : Scheme.{u}} {A : RelativeProjAlgebra X} (D : RelativeProjData A)

/-- The relative Proj scheme obtained by the specified relative scheme gluing. -/
def proj : Scheme.{u} := D.gluing.glued

/-- The structural morphism of the specified relative Proj. -/
def π : D.proj ⟶ X := D.gluing.toBase

end RelativeProjData

end AlgebraicGeometry
