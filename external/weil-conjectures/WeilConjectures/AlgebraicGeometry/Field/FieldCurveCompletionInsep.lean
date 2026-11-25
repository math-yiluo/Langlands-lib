/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import Mathlib.AlgebraicGeometry.Limits
public import Mathlib.AlgebraicGeometry.IdealSheaf.Subscheme
public import Mathlib.AlgebraicGeometry.Geometrically.Irreducible
public import Mathlib.AlgebraicGeometry.Morphisms.Smooth
public import Mathlib.AlgebraicGeometry.Morphisms.FinitePresentation
public import Mathlib.AlgebraicGeometry.Morphisms.Separated
public import Mathlib.FieldTheory.PurelyInseparable.Basic
public import Mathlib.FieldTheory.Separable
public import Mathlib.Topology.KrullDimension
public import WeilConjectures.Mathlib.AlgebraicGeometry.Normalization
public import WeilConjectures.AlgebraicGeometry.Morphisms.Projective
import Mathlib.AlgebraicGeometry.Noetherian
import WeilConjectures.AlgebraicGeometry.HomeomorphPurelyInseparableBaseChange
import WeilConjectures.AlgebraicGeometry.Projective.ProjectiveBaseChange
import WeilConjectures.AlgebraicGeometry.Proper.ProperGeometricallyReducedGlobalSectionsSeparable
import WeilConjectures.AlgebraicGeometry.SteinFactorizationAffine
import WeilConjectures.AlgebraicGeometry.ProperBaseChange.CurveProjectiveDenseCompletion
import WeilConjectures.AlgebraicGeometry.Finite.FiniteSeparableBaseRefinement
import WeilConjectures.AlgebraicGeometry.ProperBaseChange.GeonormalDimOneSmooth
import WeilConjectures.AlgebraicGeometry.ProperBaseChange.NormalizationGeonormalInsep
import WeilConjectures.AlgebraicGeometry.Finite.FiniteOverProjective
import WeilConjectures.AlgebraicGeometry.GlobalSectionsProper
import WeilConjectures.AlgebraicGeometry.Regular
import Mathlib.FieldTheory.IntermediateField.Adjoin.Algebra
import Mathlib.RingTheory.AlgebraicIndependent.Transcendental

/-!
# Smooth projective completions after an inseparable field extension

Source: Stacks Project, Varieties, Tag 0GK5,
`lemma-dim-1-projective-completion-after-insep`, assertions (1)-(5)
(blueprint: lem-weil-pbc-field-curve-completion-insep).
-/

@[expose] public section

universe u

open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry

private theorem dense_open_meets_component {T U : Scheme.{u}}
    [IsNoetherian T] (a : U ⟶ T) [IsOpenImmersion a] (ha : DenseRange a)
    (Z : Set T) (hZ : Z ∈ irreducibleComponents T) :
    (Z ∩ Set.range a).Nonempty := by
  classical
  have hfinite := finite_irreducibleComponents_of_isNoetherian (X := T)
  let W : T.Opens := ⟨(⋃₀ (irreducibleComponents T \ {Z}))ᶜ, by
    rw [Set.sUnion_eq_biUnion, isOpen_compl_iff]
    exact hfinite.sdiff.isClosed_biUnion
      (fun V hV ↦ isClosed_of_mem_irreducibleComponents V hV.1)⟩
  have hW : closure (W : Set T) = Z :=
    closure_sUnion_irreducibleComponents_sdiff_singleton hfinite Z hZ
  have hWne : (W : Set T).Nonempty := by
    by_contra! he
    exact hZ.1.nonempty.ne_empty (by rw [← hW, he, closure_empty])
  obtain ⟨x, hxW, hxU⟩ := ha.inter_open_nonempty W W.isOpen hWne
  exact ⟨x, by rw [← hW]; exact subset_closure hxW, hxU⟩

private theorem component_preimage_surjective {T U : Scheme.{u}}
    (a : U ⟶ T) [IsOpenImmersion a]
    (R : Set U) (hR : R ∈ irreducibleComponents U) :
    ∃ Z ∈ irreducibleComponents T, a ⁻¹' Z = R := by
  obtain ⟨Z, hZ, hsub⟩ := exists_mem_irreducibleComponents_subset_of_isIrreducible
    (a '' R) (hR.1.image a a.continuous.continuousOn)
  have hmeet : (Z ∩ Set.range a).Nonempty := by
    obtain ⟨x, hx⟩ := hR.1.nonempty
    exact ⟨a x, hsub ⟨x, hx, rfl⟩, x, rfl⟩
  have hp := preimage_mem_irreducibleComponents hZ a.isOpenEmbedding hmeet
  exact ⟨Z, hZ, Set.Subset.antisymm (hR.2 hp.1 (Set.image_subset_iff.mp hsub))
    (Set.image_subset_iff.mp hsub)⟩

private theorem normalization_iso_of_iso_over {X Y T : Scheme.{u}}
    (f : X ⟶ T) (g : Y ⟶ T) [QuasiCompact f] [QuasiSeparated f]
    [QuasiCompact g] [QuasiSeparated g] (e : X ≅ Y) (he : e.hom ≫ g = f) :
    ∃ E : f.normalization ≅ g.normalization,
      E.hom ≫ g.fromNormalization = f.fromNormalization := by
  have hi : e.inv ≫ f = g := by rw [← he]; simp
  let a := f.normalizationDesc (e.hom ≫ g.toNormalization) g.fromNormalization
    (by simp [he])
  let b := g.normalizationDesc (e.inv ≫ f.toNormalization) f.fromNormalization
    (by simp [hi])
  have hab : a ≫ b = 𝟙 _ := by
    apply Scheme.Hom.normalization.hom_ext _ _ _ f.fromNormalization
    · simp [a, b]
    · simp [a, b]
    · simp
  have hba : b ≫ a = 𝟙 _ := by
    apply Scheme.Hom.normalization.hom_ext _ _ _ g.fromNormalization
    · simp [a, b]
    · simp [a, b]
    · simp
  exact ⟨⟨a, b, hab, hba⟩, by simp [a]⟩

private theorem normalization_open_immersion {C T : Scheme.{u}}
    [IsIntegral C] [IsIntegral T] (c : C ⟶ T) [IsOpenImmersion c] :
    ∃ j : C.normalization ⟶ T.normalization,
      IsOpenImmersion j ∧ DenseRange j ∧
      j ≫ T.fromNormalization = C.fromNormalization ≫ c := by
  have : IsDominant c := ⟨c.isOpenEmbedding.isOpen_range.dense
    (Set.range_nonempty c)⟩
  have hη : c (genericPoint C) = genericPoint T := by
    refine ((genericPoint_spec T).eq ?_).symm
    have h := (genericPoint_spec C).image c.continuous
    rwa [Set.image_univ, c.denseRange.closure_range] at h
  have key (x : C) (y : T) (h : c x = y) :
      ∃ e : Spec (C.presheaf.stalk x) ≅ Spec (T.presheaf.stalk y),
        e.hom ≫ T.fromSpecStalk y = C.fromSpecStalk x ≫ c := by
    subst y
    exact ⟨asIso (Spec.map (c.stalkMap x)), Scheme.SpecMap_stalkMap_fromSpecStalk c⟩
  obtain ⟨e, he⟩ := key (genericPoint C) (genericPoint T) hη
  have H : IsPullback C.fromSpecFunctionField e.hom c T.fromSpecFunctionField := by
    apply IsOpenImmersion.isPullback
    · exact he
    · ext z
      change T.fromSpecFunctionField z ∈ Set.range c ↔ z ∈ Set.range e.hom
      constructor
      · intro _
        exact e.hom.surjective z
      · rintro ⟨x, rfl⟩
        exact ⟨C.fromSpecFunctionField x, (congrArg (fun f ↦ f x) he).symm⟩
  obtain ⟨E, hE⟩ := normalization_iso_of_iso_over C.fromSpecFunctionField
    (pullback.snd T.fromSpecFunctionField c) H.flip.isoPullback
    H.flip.isoPullback_hom_snd
  let j := E.hom ≫ T.fromSpecFunctionField.normalizationPullback c ≫
    pullback.fst T.fromNormalization c
  have hj : IsOpenImmersion j := by dsimp only [j]; infer_instance
  let := hj
  exact ⟨j, hj, j.isOpenEmbedding.isOpen_range.dense (Set.range_nonempty j), by
    dsimp only [j]
    rw [Category.assoc, Category.assoc, pullback.condition]
    rw [Scheme.Hom.normalizationPullback_snd_assoc, ← Category.assoc, hE]⟩

private theorem separable_of_finite_separableExtension
    (k L : Type u) [Field k] [Field L] [Algebra k L] [Module.Finite k L]
    (h : Algebra.IsSeparableExtension k L) : Algebra.IsSeparable k L := by
  obtain ⟨s, hs, hsep⟩ := h ⊤ (IntermediateField.fg_top k L)
  have hsempty : s = ∅ := by
    have : IsEmpty s := hs.1.isEmpty_of_isAlgebraic
    exact Set.isEmpty_coe_sort.mp this
  subst s
  rw [IntermediateField.adjoin_empty] at hsep
  let := hsep
  have : Algebra.IsSeparable k (⊤ : IntermediateField k L) := by
    apply Algebra.IsSeparable.of_equiv_equiv
      (IntermediateField.botEquiv k (⊤ : IntermediateField k L)).toRingEquiv
      (RingEquiv.refl (⊤ : IntermediateField k L))
    ext x
    obtain ⟨y, rfl⟩ := (IntermediateField.botEquiv k
      (⊤ : IntermediateField k L)).symm.surjective x
    simp only [RingHom.comp_apply, RingEquiv.coe_toRingHom,
      RingEquiv.refl_apply, IntermediateField.botEquiv_symm,
      ← IsScalarTower.algebraMap_apply]
    exact congrArg (fun z : k ↦ ((algebraMap k (⊤ : IntermediateField k L)) z).1)
      (IntermediateField.botEquiv_def (F := k) (E := (⊤ : IntermediateField k L)) y)
  exact AlgEquiv.Algebra.isSeparable (IntermediateField.topEquiv :
    (⊤ : IntermediateField k L) ≃ₐ[k] L)

private theorem constant_field_model
    (k : Type u) [Field k] (B : Scheme.{u}) (b : B ⟶ Spec (.of k))
    [IsIntegral B] [Smooth b] [IsHProjective b] :
    ∃ (L : Type u) (_ : Field L) (_ : Algebra k L)
      (q : B ⟶ Spec (.of L)),
      Module.Finite k L ∧ Algebra.IsSeparable k L ∧
      q ≫ Spec.map (CommRingCat.ofHom (algebraMap k L)) = b ∧
      Smooth q ∧ IsHProjective q ∧ GeometricallyIrreducible q := by
  let : B.Over (Spec (.of k)) := ⟨b⟩
  have hb : B ↘ Spec (.of k) = b := rfl
  have : IsProper (B ↘ Spec (.of k)) := by rw [hb]; infer_instance
  have : GeometricallyReduced (B ↘ Spec (.of k)) := by
    rw [hb]; exact Smooth.geometricallyReduced b
  have hA : IsField Γ(B, ⊤) := Scheme.isField_globalSections_of_universallyClosed (k := k)
  let L := Γ(B, ⊤)
  let : Field L := hA.toField
  let : Algebra k L := (Scheme.globalSectionsRingHom k (X := B)).toAlgebra
  have : Module.Finite k L := Scheme.finite_globalSectionsRingHom_of_isProper
  have : GeometricallyReduced b := Smooth.geometricallyReduced b
  have hsep : Algebra.IsSeparable k L := separable_of_finite_separableExtension k L
    (proper_geometricallyReduced_globalSections_isSeparable k B hA)
  let := hsep
  let q : B ⟶ Spec (.of L) := B.toSpecΓ
  have hqb : q ≫ Spec.map (CommRingCat.ofHom (algebraMap k L)) = b := by
    change B.toSpecΓ ≫ Spec.map ((Scheme.ΓSpecIso (.of k)).inv ≫ b.appTop) = b
    rw [Spec.map_comp, ← Scheme.toSpecΓ_naturality_assoc]
    simp
  have : Smooth (q ≫ Spec.map (CommRingCat.ofHom (algebraMap k L))) := by
    rw [hqb]; infer_instance
  have : IsHProjective (q ≫ Spec.map (CommRingCat.ofHom (algebraMap k L))) := by
    rw [hqb]; infer_instance
  obtain ⟨hs, hp, _⟩ := smooth_hProjective_proper_of_finite_separable_base k L B q
  let := hs
  have : GeometricallyConnected q := (b.steinFactorization_affine).2.2.1
  exact ⟨L, inferInstance, inferInstance, q, inferInstance, hsep, hqb, hs, hp,
    GeometricallyIrreducible.of_smooth_of_geometricallyConnected q⟩

/-- A separated finite type scheme of dimension at most one has, after finite purely
inseparable extension, componentwise normalization with smooth projective geometrically
irreducible completions over finite separable constant fields.
Source: Stacks Project, Varieties, Tag 0GK5
(blueprint: lem-weil-pbc-field-curve-completion-insep).

The integral closed immersions `c i` enumerate the reduced irreducible components of
`X_K`: an integral closed subscheme with a given irreducible-component support is exactly
its reduced induced subscheme, equivalently that of `(X_K)_red`. The isomorphisms `e i`
identify `Y i` with their normalizations. Thus the equation for `ν` specifies the full
componentwise normalization map, including its scheme structure.

Proof:
1. Take a dense projective completion of X and a finite purely inseparable extension
   making its componentwise normalization geometrically normal. This applies directly
   to nonreduced and empty schemes. The base-change projection is a homeomorphism,
   preserving the dimension bound and the dense original open.
2. Each normalized component is finite over a closed component of the projective
   completion, hence projective. Its dimension is at most one. Geometric normality
   descends from the normalization coproduct along the component open immersions;
   the geometric-normality dimension-one criterion gives smoothness.
3. The global sections of each proper integral component form a finite field extension;
   smoothness makes it separable. Affine Stein factorization gives geometric connectedness
   over this constant field, and finite separable base refinement preserves smoothness
   and projectivity. Smooth geometrically connected schemes over a field are geometrically
   irreducible, by regularity and the regular connected integral criterion.
4. Pull back the reduced integral closed components to the original dense open. They are
   nonempty integral schemes and enumerate its irreducible components without repetitions.
   Normalization commutes with their open immersions by Mathlib smooth normalization base
   change, giving the dense open immersions of their normalizations into the completions.
5. Finite normalization and finite-type composition give the finite-presentation clauses
   over the Noetherian field base. The normalization coproduct has a finite compact open
   cover. The component enumeration and nonemptiness identify the empty-index case with
   empty X, and the pullback equations give all structure-map identities.
-/
theorem exists_field_curve_completion_insep
    (k : Type u) [Field k] (X : Scheme.{u}) [X.Over (Spec (.of k))]
    [IsSeparated (X ↘ Spec (.of k))] [LocallyOfFiniteType (X ↘ Spec (.of k))]
    [QuasiCompact (X ↘ Spec (.of k))] (hdim : topologicalKrullDim X ≤ 1) :
    ∃ (K : Type u) (_ : Field K) (_ : Algebra k K),
      Module.Finite k K ∧ IsPurelyInseparable k K ∧
      ∃ (n : ℕ) (C : Fin n → Scheme.{u}) (hC : ∀ i, IsIntegral (C i))
        (c : ∀ i, C i ⟶ pullback (X ↘ Spec (.of k))
          (Spec.map (CommRingCat.ofHom (algebraMap k K))))
        (Y B : Fin n → Scheme.{u})
        (e : ∀ i, Y i ≅ @Scheme.normalization (C i) (hC i))
        (j : ∀ i, Y i ⟶ B i)
        (L : Fin n → Type u) (_ : ∀ i, Field (L i)) (_ : ∀ i, Algebra K (L i))
        (q : ∀ i, B i ⟶ Spec (.of (L i)))
        (p : ∀ i, Y i ⟶ Spec (.of K))
        (ν : (∐ Y) ⟶ pullback (X ↘ Spec (.of k))
          (Spec.map (CommRingCat.ofHom (algebraMap k K)))),
        (∀ i, IsClosedImmersion (c i) ∧
          Set.range (c i) ∈ irreducibleComponents
            (pullback (X ↘ Spec (.of k))
              (Spec.map (CommRingCat.ofHom (algebraMap k K))) : Scheme.{u})) ∧
        Function.Injective (fun i ↦ Set.range (c i)) ∧
        (∀ Z ∈ irreducibleComponents
          (pullback (X ↘ Spec (.of k))
            (Spec.map (CommRingCat.ofHom (algebraMap k K))) : Scheme.{u}),
          ∃ i, Set.range (c i) = Z) ∧
        ν = Sigma.desc (fun i ↦ (e i).hom ≫ @Scheme.fromNormalization (C i) (hC i) ≫ c i) ∧
        (∀ i, Module.Finite K (L i) ∧ Algebra.IsSeparable K (L i) ∧
          IsOpenImmersion (j i) ∧ DenseRange (j i) ∧ Nonempty (Y i) ∧
          Smooth (q i) ∧ IsHProjective (q i) ∧ GeometricallyIrreducible (q i) ∧
          topologicalKrullDim (B i) ≤ 1 ∧
          (e i).hom ≫ @Scheme.fromNormalization (C i) (hC i) ≫ c i ≫
            pullback.snd (X ↘ Spec (.of k))
              (Spec.map (CommRingCat.ofHom (algebraMap k K))) = p i ∧
          j i ≫ q i ≫ Spec.map (CommRingCat.ofHom (algebraMap K (L i))) = p i ∧
          LocallyOfFinitePresentation (p i) ∧ QuasiCompact (p i) ∧ QuasiSeparated (p i) ∧
          LocallyOfFinitePresentation
            (q i ≫ Spec.map (CommRingCat.ofHom (algebraMap K (L i)))) ∧
          QuasiCompact (q i ≫ Spec.map (CommRingCat.ofHom (algebraMap K (L i)))) ∧
          QuasiSeparated (q i ≫ Spec.map (CommRingCat.ofHom (algebraMap K (L i)))) ∧
          LocallyOfFinitePresentation (Spec.map (CommRingCat.ofHom (algebraMap K (L i)))) ∧
          QuasiCompact (Spec.map (CommRingCat.ofHom (algebraMap K (L i)))) ∧
          QuasiSeparated (Spec.map (CommRingCat.ofHom (algebraMap K (L i))))) ∧
        LocallyOfFinitePresentation (Sigma.desc p) ∧
        QuasiCompact (Sigma.desc p) ∧ QuasiSeparated (Sigma.desc p) ∧
        LocallyOfFinitePresentation (pullback.snd (X ↘ Spec (.of k))
          (Spec.map (CommRingCat.ofHom (algebraMap k K)))) ∧
        QuasiCompact (pullback.snd (X ↘ Spec (.of k))
          (Spec.map (CommRingCat.ofHom (algebraMap k K)))) ∧
        QuasiSeparated (pullback.snd (X ↘ Spec (.of k))
          (Spec.map (CommRingCat.ofHom (algebraMap k K)))) ∧
        (n = 0 ↔ IsEmpty X) := by
  classical
  obtain ⟨D, d, a, hd, hdimD, ha, had, hadense, _⟩ :=
    exists_projective_dense_completion_of_dim_le_one (k := k) (X := X) hdim
  let := hd
  let := ha
  let : D.Over (Spec (.of k)) := ⟨d⟩
  have hd' : D ↘ Spec (.of k) = d := rfl
  have : LocallyOfFiniteType (D ↘ Spec (.of k)) := by rw [hd']; infer_instance
  have : QuasiCompact (D ↘ Spec (.of k)) := by rw [hd']; infer_instance
  obtain ⟨K, hK, hAlg, hfin, hpi, n, Z, hZ, z, hz, hinj, hcover, hnormal⟩ :=
    exists_finite_purelyInseparable_geometricallyNormal_normalization k D
  let := hK
  let := hAlg
  let := hfin
  let := hpi
  let b := Spec.map (CommRingCat.ofHom (algebraMap k K))
  let T := pullback d b
  let t : T ⟶ Spec (.of K) := pullback.snd d b
  let X' := pullback (X ↘ Spec (.of k)) b
  let x' : X' ⟶ Spec (.of K) := pullback.snd _ _
  change ∀ i, IsClosedImmersion (z i) at hz
  let (i : Fin n) : IsIntegral (Z i) := hZ i
  let (i : Fin n) : IsClosedImmersion (z i) := hz i
  have hzcomp (i : Fin n) : Set.range (z i) ∈ irreducibleComponents T :=
    (hcover _).mpr ⟨i, rfl⟩
  have : IsProjective d := IsHProjective.isProjective d
  have : IsProjective t := projective_base_change d b
  have : IsHProjective t := inferInstance
  have hdimT : topologicalKrullDim T ≤ 1 := by
    have hp := isHomeomorph_baseChange_of_isPurelyInseparable k K D
    exact (IsHomeomorph.topologicalKrullDim_eq _ hp).le.trans hdimD
  let B (i : Fin n) := (Z i).normalization
  let v : (∐ B) ⟶ T := Sigma.desc (fun i ↦ (Z i).fromNormalization ≫ z i)
  let bi (i : Fin n) : B i ⟶ Spec (.of K) := (Z i).fromNormalization ≫ z i ≫ t
  have hBproj (i : Fin n) : IsHProjective (bi i) := by
    have : IsFinite (Z i).fromNormalization :=
      (Z i).isFinite_fromNormalization_of_locallyOfFiniteType (z i ≫ t)
    have : IsProjective ((Z i).fromNormalization ≫ z i ≫ t) := by
      simpa only [Category.assoc] using
        (finite_over_projective_affineLocally t ((Z i).fromNormalization ≫ z i)).2
          (inferInstance : IsAffine (Spec (.of K)))
    infer_instance
  let (i : Fin n) : IsHProjective (bi i) := hBproj i
  have hBdim (i : Fin n) : topologicalKrullDim (B i) ≤ 1 := by
    rw [(Z i).topologicalKrullDim_normalization (z i ≫ t)]
    exact ((z i).isClosedEmbedding.isInducing.topologicalKrullDim_le).trans hdimT
  have hBsmooth (i : Fin n) : Smooth (bi i) := by
    let : (B i).Over (Spec (.of K)) := ⟨bi i⟩
    have hbi : B i ↘ Spec (.of K) = bi i := rfl
    have : LocallyOfFiniteType (B i ↘ Spec (.of K)) := by rw [hbi]; infer_instance
    have : QuasiCompact (B i ↘ Spec (.of K)) := by rw [hbi]; infer_instance
    apply (smooth_and_geometricallyReduced_of_geonormal_dim_le_one K (B i)
      (hBdim i) ?_).1
    intro L _ _ w
    let bL := Spec.map (CommRingCat.ofHom (algebraMap K L))
    let g := pullback.map (bi i) bL (v ≫ t) bL (Sigma.ι B i) (𝟙 _) (𝟙 _)
      (by simp [bi, v]) (by simp)
    have : IsOpenImmersion g := by dsimp only [g]; infer_instance
    obtain ⟨hd, hc⟩ := hnormal L (g w)
    have : IsDomain ((pullback (v ≫ t) bL).presheaf.stalk (g w)) := hd
    have : IsIntegrallyClosed ((pullback (v ≫ t) bL).presheaf.stalk (g w)) := hc
    let e := (asIso (g.stalkMap w)).commRingCatIsoToRingEquiv
    exact ⟨e.symm.toMulEquiv.isDomain, IsIntegrallyClosed.of_equiv e⟩
  let (i : Fin n) : Smooth (bi i) := hBsmooth i
  choose L hL hKL q hqfin hqsep hqcomp hqsmooth hqproj hqirr using
    fun i ↦ constant_field_model K (B i) (bi i)
  let (i : Fin n) : Field (L i) := hL i
  let (i : Fin n) : Algebra K (L i) := hKL i
  let a' : X' ⟶ T := pullback.map _ _ _ _ a (𝟙 _) (𝟙 _) (by simpa using had.symm) (by simp)
  have ha' : IsOpenImmersion a' := by dsimp only [a']; infer_instance
  let := ha'
  have ha'fst : a' ≫ pullback.fst d b = pullback.fst (X ↘ Spec (.of k)) b ≫ a := by
    simp [a']
  have ha'snd : a' ≫ t = x' := by simp [a', t, x']
  have ha'dense : DenseRange a' := by
    have hpD := isHomeomorph_baseChange_of_isPurelyInseparable k K D
    have hpX := isHomeomorph_baseChange_of_isPurelyInseparable k K X
    have hrange : Set.range a' = (pullback.fst d b) ⁻¹' Set.range a := by
      ext z
      constructor
      · rintro ⟨w, rfl⟩
        exact ⟨pullback.fst (X ↘ Spec (.of k)) b w,
          (congrArg (fun f ↦ f w) ha'fst).symm⟩
      · rintro ⟨x, hx⟩
        obtain ⟨w, hw⟩ := (show Function.Surjective
          (pullback.fst (X ↘ Spec (.of k)) b) from hpX.surjective) x
        refine ⟨w, hpD.injective ?_⟩
        change (a' ≫ pullback.fst d b) w = _
        rw [ha'fst]
        change (pullback.fst (X ↘ Spec (.of k)) b) w = x at hw
        change a ((pullback.fst (X ↘ Spec (.of k)) b) w) = (pullback.fst d b) z
        rw [hw]
        exact hx
    change Dense (Set.range a')
    rw [hrange]
    exact hadense.preimage hpD.isOpenMap
  have : IsLocallyNoetherian T := LocallyOfFiniteType.isLocallyNoetherian t
  have : CompactSpace T := QuasiCompact.compactSpace_of_compactSpace t
  have : IsNoetherian T := ⟨⟩
  let C (i : Fin n) := pullback a' (z i)
  let c (i : Fin n) : C i ⟶ X' := pullback.fst a' (z i)
  let r (i : Fin n) : C i ⟶ Z i := pullback.snd a' (z i)
  have hCrange (i : Fin n) : Set.range (c i) = a' ⁻¹' Set.range (z i) :=
    Scheme.Pullback.range_fst a' (z i)
  have hCne (i : Fin n) : Nonempty (C i) := by
    obtain ⟨x, hxZ, y, hy⟩ := dense_open_meets_component a' ha'dense _ (hzcomp i)
    obtain ⟨w, hw⟩ := hxZ
    obtain ⟨p, _, _⟩ := Scheme.Pullback.exists_preimage_pullback y w (hy.trans hw.symm)
    exact ⟨p⟩
  let (i : Fin n) : Nonempty (C i) := hCne i
  have hCint (i : Fin n) : IsIntegral (C i) := isIntegral_of_isOpenImmersion (r i)
  let (i : Fin n) : IsIntegral (C i) := hCint i
  choose j hj hjdense hjcomp using fun i ↦ normalization_open_immersion (r i)
  let Y (i : Fin n) := (C i).normalization
  let p (i : Fin n) : Y i ⟶ Spec (.of K) := (C i).fromNormalization ≫ c i ≫ x'
  let ν : (∐ Y) ⟶ X' := Sigma.desc (fun i ↦ (C i).fromNormalization ≫ c i)
  have hCcomp (i : Fin n) : Set.range (c i) ∈ irreducibleComponents X' := by
    rw [hCrange]
    exact preimage_mem_irreducibleComponents (hzcomp i) a'.isOpenEmbedding
      (dense_open_meets_component a' ha'dense _ (hzcomp i))
  have hclosure (i : Fin n) : closure (a' '' Set.range (c i)) = Set.range (z i) := by
    rw [hCrange]
    apply closure_image_preimage_of_isPreirreducible a' a'.isOpenEmbedding.isOpenMap
    · rw [← hCrange]
      exact Set.range_nonempty (c i)
    · exact (hzcomp i).1.2
    · exact isClosed_of_mem_irreducibleComponents _ (hzcomp i)
  have hCinj : Function.Injective (fun i ↦ Set.range (c i)) := by
    intro i j hij
    apply hinj
    change Set.range (z i) = Set.range (z j)
    change Set.range (c i) = Set.range (c j) at hij
    exact (hclosure i).symm.trans
      ((congrArg (fun S : Set X' ↦ closure (a' '' S)) hij).trans (hclosure j))
  have hCcover : ∀ W ∈ irreducibleComponents X', ∃ i, Set.range (c i) = W := by
    intro W hW
    obtain ⟨V, hV, hVW⟩ := component_preimage_surjective a' W hW
    obtain ⟨i, hi⟩ := (hcover V).mp hV
    exact ⟨i, by rw [hCrange, hi, hVW]⟩
  let (i : Fin n) : IsOpenImmersion (j i) := hj i
  let (i : Fin n) : IsFinite (C i).fromNormalization :=
    (C i).isFinite_fromNormalization_of_locallyOfFiniteType (c i ≫ x')
  let (i : Fin n) : Module.Finite K (L i) := hqfin i
  let (i : Fin n) : Algebra.IsSeparable K (L i) := hqsep i
  let (i : Fin n) : Smooth (q i) := hqsmooth i
  let (i : Fin n) : IsHProjective (q i) := hqproj i
  let (i : Fin n) : IsFinite (Spec.map (CommRingCat.ofHom (algebraMap K (L i)))) := by
    rw [IsFinite.SpecMap_iff]
    exact RingHom.finite_algebraMap.mpr (hqfin i)
  have hpcomp (i : Fin n) : j i ≫ bi i = p i := by
    dsimp only [bi, p]
    rw [← Category.assoc, ← Category.assoc, hjcomp]
    dsimp only [r, c]
    simp only [Category.assoc]
    rw [← pullback.condition_assoc, ha'snd]
  let (i : Fin n) : LocallyOfFiniteType (p i) := by dsimp only [p]; infer_instance
  let (i : Fin n) : QuasiCompact (p i) := by dsimp only [p]; infer_instance
  let (i : Fin n) : IsSeparated (p i) := by dsimp only [p]; infer_instance
  let (i : Fin n) : CompactSpace (Y i) :=
    QuasiCompact.compactSpace_of_compactSpace (p i)
  let 𝒰 := sigmaOpenCover Y
  have : Finite 𝒰.I₀ := by
    change Finite (Fin n)
    infer_instance
  have : ∀ i, CompactSpace (𝒰.X i) := by
    change ∀ i, CompactSpace (Y i)
    infer_instance
  have : CompactSpace (∐ Y : Scheme.{u}) := 𝒰.compactSpace
  have : LocallyOfFiniteType (Sigma.desc p) :=
    IsZariskiLocalAtSource.sigmaDesc fun i ↦ inferInstance
  have : IsLocallyNoetherian (∐ Y) :=
    LocallyOfFiniteType.isLocallyNoetherian (Sigma.desc p)
  have hnempty : n = 0 ↔ IsEmpty X := by
    constructor
    · intro hn
      have he : IsEmpty X' := ⟨fun x ↦ by
        obtain ⟨i, hi⟩ := hCcover (irreducibleComponent x)
          (irreducibleComponent_mem_irreducibleComponents x)
        subst n
        exact Fin.elim0 i⟩
      have hpX := isHomeomorph_baseChange_of_isPurelyInseparable k K X
      exact ⟨fun x ↦ by obtain ⟨y, _⟩ := hpX.surjective x; exact he.false y⟩
    · intro he
      by_contra hn
      let i : Fin n := ⟨0, Nat.pos_of_ne_zero hn⟩
      obtain ⟨y⟩ := hCne i
      exact he.false (pullback.fst (X ↘ Spec (.of k)) b (c i y))
  refine ⟨K, hK, hAlg, hfin, hpi, n, C, hCint, c, Y, B,
    fun i ↦ Iso.refl _, j, L, hL, hKL, q, p, ν, ?_⟩
  refine ⟨fun i ↦ ⟨inferInstance, hCcomp i⟩, hCinj, hCcover, ?_, ?_,
    ?_, ?_, ?_, ?_, ?_, ?_, hnempty⟩
  · simp only [ν, Iso.refl_hom, Category.id_comp]
    rfl
  · intro i
    refine ⟨hqfin i, hqsep i, hj i, hjdense i, inferInstance,
      hqsmooth i, hqproj i, hqirr i, hBdim i, ?_, ?_,
      inferInstance, inferInstance, inferInstance, ?_, ?_, ?_, ?_, ?_, ?_⟩
    · simp only [Iso.refl_hom, Category.id_comp]
      rfl
    · rw [hqcomp, hpcomp]
    all_goals infer_instance
  all_goals infer_instance

end AlgebraicGeometry
