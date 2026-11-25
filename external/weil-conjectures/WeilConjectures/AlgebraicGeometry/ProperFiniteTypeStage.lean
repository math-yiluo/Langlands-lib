/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import Mathlib.AlgebraicGeometry.Morphisms.Proper
public import Mathlib.Order.Interval.Set.Basic
public import Mathlib.Order.Interval.Set.Final
public import WeilConjectures.AlgebraicGeometry.GeometricFibreDimension
public import WeilConjectures.Mathlib.Algebra.Category.Ring.FilteredColimits
public import WeilConjectures.Mathlib.AlgebraicGeometry.AffineTransitionLimit
import WeilConjectures.AlgebraicGeometry.EventuallyProper

/-!
# Proper morphisms over a limit descend to a proper stage

Let `{Dᵢ}` be a directed inverse system of quasi-compact quasi-separated schemes with affine
transition maps and limit `S`, and let `b : Y ⟶ S` be proper and locally of finite
presentation.

- `AlgebraicGeometry.Scheme.exists_isProper_isPullback_of_isLimit`: `b` is the base change of a
  proper morphism `p : Y₀ ⟶ Dₗ` at some stage (Stacks, Tags 01ZM and 081F).
- `AlgebraicGeometry.baseChangeIciDiagram`, `AlgebraicGeometry.baseChangeIciCone`,
  `AlgebraicGeometry.isLimitBaseChangeIciCone`: then `Y` is the limit of the directed system
  `{ Y₀ ×_{Dₗ} Dᵢ }_{i ≥ l}`.

For an affine scheme `S` and a field `k` with a `k`-algebra structure on `Γ(S, ⊤)`, `S` is the
limit of the spectra of the finitely generated `k`-subalgebras of `Γ(S, ⊤)`, which are of finite
type over `k` (`AlgebraicGeometry.isLimitFGSubalgebraSpecCone`). Hence:

- `AlgebraicGeometry.exists_topologicalKrullDim_pullback_le_of_isProper_of_isNoetherian`: the
  fibres of a proper morphism to a Noetherian scheme over a field have bounded dimension.
-/

@[expose] public section

universe u

open CategoryTheory Limits Opposite

namespace AlgebraicGeometry

section Directed

variable {I : Type u} [Preorder I] {D : Iᵒᵖ ⥤ Scheme.{u}} {c : Cone D}

/-- **Proper morphisms descend to a proper stage** (Stacks, Tags 01ZM and 081F). Let `{Dᵢ}` be a
directed inverse system of quasi-compact quasi-separated schemes with affine transition maps and
limit cone `c`. A proper morphism `b : Y ⟶ lim Dᵢ` locally of finite presentation is the base
change of a proper morphism `p : Y₀ ⟶ Dᵢ` locally of finite presentation at some stage. -/
theorem Scheme.exists_isProper_isPullback_of_isLimit [IsDirectedOrder I] [Nonempty I]
    [∀ {i j : Iᵒᵖ} (f : i ⟶ j), IsAffineHom (D.map f)] [∀ i, CompactSpace (D.obj i)]
    [∀ i, QuasiSeparatedSpace (D.obj i)] (hc : IsLimit c) {Y : Scheme.{u}}
    (b : Y ⟶ c.pt) [IsProper b] [LocallyOfFinitePresentation b] :
    ∃ (i : I) (Y₀ : Scheme.{u}) (p : Y₀ ⟶ D.obj (op i)) (h : Y ⟶ Y₀),
      IsProper p ∧ LocallyOfFinitePresentation p ∧ IsPullback h b p (c.π.app (op i)) := by
  obtain ⟨j, Y₀, p, hfp, hqc, hqs, h, H⟩ := Scheme.exists_isPullback_of_finitePresentation hc b
  have : CompactSpace Y₀ := QuasiCompact.compactSpace_of_compactSpace p
  have : QuasiSeparatedSpace Y₀ := quasiSeparatedSpace_of_quasiSeparated p
  have hs : IsProper (pullback.snd p (c.π.app j)) := by
    rw [← H.isoPullback_inv_snd]
    infer_instance
  let ψ := pullback.map p (c.π.app j) (𝟙 (D.obj j)) (c.π.app j) p (𝟙 c.pt) (𝟙 (D.obj j))
    (Category.comp_id p) ((Category.comp_id _).trans (Category.id_comp _).symm)
  have hψ : IsProper ψ := by
    have he : ψ ≫ pullback.snd (𝟙 (D.obj j)) (c.π.app j) = pullback.snd p (c.π.app j) := by
      simp [ψ]
    rw [← he] at hs
    exact (MorphismProperty.cancel_right_of_respectsIso @IsProper _ _).mp hs
  obtain ⟨l, hjl, hl⟩ := exists_isProper_baseChange_of_isLimit D c hc j.unop p (𝟙 (D.obj j)) p
    (by simp) hψ
  let t := D.map (homOfLE hjl).op
  have hp' : IsProper (pullback.snd p t) := by
    have he : pullback.map p t (𝟙 (D.obj j)) t p (𝟙 (D.obj (op l))) (𝟙 (D.obj j))
        (Category.comp_id p) (Category.comp_id t) ≫ pullback.snd (𝟙 (D.obj j)) t =
          pullback.snd p t := by
      simp
    rw [← he]
    infer_instance
  let h' : Y ⟶ pullback p t := pullback.lift h (b ≫ c.π.app (op l)) (by
    rw [Category.assoc, c.w (homOfLE hjl).op, H.w])
  refine ⟨l, pullback p t, pullback.snd p t, h', hp', inferInstance, ?_⟩
  refine IsPullback.of_right ?_ (pullback.lift_snd _ _ _) (IsPullback.of_hasPullback p t)
  rw [pullback.lift_fst, c.w]
  exact H

variable (D) (l : I) {Y₀ : Scheme.{u}} (p : Y₀ ⟶ D.obj (op l))

instance [IsDirectedOrder I] (l : I) : IsDirectedOrder (Set.Ici l) where
  directed i j := by
    obtain ⟨k, hik, hjk⟩ := directed_of (· ≤ ·) i.1 j.1
    exact ⟨⟨k, i.2.trans hik⟩, hik, hjk⟩

instance [IsDirectedOrder I] (l : I) : (Subtype.mono_coe (· ∈ Set.Ici l)).functor.Final := by
  rw [Monotone.final_functor_iff]
  intro k
  obtain ⟨m, hlm, hkm⟩ := directed_of (· ≤ ·) l k
  exact ⟨⟨m, hlm⟩, hkm⟩

/-- The base change `{ Y₀ ×_{Dₗ} Dᵢ }_{i ≥ l}` of the directed system `{Dᵢ}` along a morphism
`p : Y₀ ⟶ Dₗ`, indexed by the stages above `l`. -/
@[simps]
noncomputable def baseChangeIciDiagram : (Set.Ici l)ᵒᵖ ⥤ Scheme.{u} where
  obj i := pullback p (D.map (homOfLE i.unop.2).op)
  map {i j} f := pullback.map _ _ _ _ (𝟙 Y₀)
    (D.map ((Subtype.mono_coe (· ∈ Set.Ici l)).functor.op.map f)) (𝟙 _)
    (by simp) (by rw [Category.comp_id, ← D.map_comp]; rfl)
  map_id i := by apply pullback.hom_ext <;> simp
  map_comp f g := by apply pullback.hom_ext <;> simp

lemma isPullback_baseChangeIciDiagram_map {i j : (Set.Ici l)ᵒᵖ} (f : i ⟶ j) :
    IsPullback ((baseChangeIciDiagram D l p).map f) (pullback.snd p (D.map (homOfLE i.unop.2).op))
      (pullback.snd p (D.map (homOfLE j.unop.2).op))
      (D.map ((Subtype.mono_coe (· ∈ Set.Ici l)).functor.op.map f)) :=
  isPullback_pullback_map _ _ _ _ (by rw [← D.map_comp]; rfl)

instance [∀ {i j : Iᵒᵖ} (f : i ⟶ j), IsAffineHom (D.map f)] {i j : (Set.Ici l)ᵒᵖ}
    (f : i ⟶ j) : IsAffineHom ((baseChangeIciDiagram D l p).map f) :=
  MorphismProperty.of_isPullback (P := @IsAffineHom)
    (isPullback_baseChangeIciDiagram_map D l p f).flip inferInstance

instance [∀ {i j : Iᵒᵖ} (f : i ⟶ j), IsAffineHom (D.map f)] [CompactSpace Y₀]
    (i : (Set.Ici l)ᵒᵖ) : CompactSpace ((baseChangeIciDiagram D l p).obj i) :=
  have : IsAffineHom (pullback.fst p (D.map (homOfLE i.unop.2).op)) :=
    MorphismProperty.pullback_fst _ _ inferInstance
  QuasiCompact.compactSpace_of_compactSpace (pullback.fst p (D.map (homOfLE i.unop.2).op))

instance [∀ {i j : Iᵒᵖ} (f : i ⟶ j), IsAffineHom (D.map f)] [QuasiSeparatedSpace Y₀]
    (i : (Set.Ici l)ᵒᵖ) : QuasiSeparatedSpace ((baseChangeIciDiagram D l p).obj i) :=
  have : IsAffineHom (pullback.fst p (D.map (homOfLE i.unop.2).op)) :=
    MorphismProperty.pullback_fst _ _ inferInstance
  quasiSeparatedSpace_of_quasiSeparated (pullback.fst p (D.map (homOfLE i.unop.2).op))

/-- (Implementation) The projection from the base changed system to the system `{Dᵢ}_{i ≥ l}`. -/
@[simps]
noncomputable def baseChangeIciDiagramπ :
    baseChangeIciDiagram D l p ⟶ (Subtype.mono_coe (· ∈ Set.Ici l)).functor.op ⋙ D where
  app i := pullback.snd _ _
  naturality i j f := by simp

variable {D l p} {Y : Scheme.{u}} {b : Y ⟶ c.pt} {h : Y ⟶ Y₀}

/-- The cone with point `Y` over the base changed system `{ Y₀ ×_{Dₗ} Dᵢ }_{i ≥ l}`, for a
cartesian square `h : Y ⟶ Y₀`, `b : Y ⟶ lim Dᵢ`, `p : Y₀ ⟶ Dₗ`. -/
@[simps]
noncomputable def baseChangeIciCone (H : IsPullback h b p (c.π.app (op l))) :
    Cone (baseChangeIciDiagram D l p) where
  pt := Y
  π.app i := pullback.lift h (b ≫ c.π.app (op i.unop.1)) (by
    rw [Category.assoc, c.w, H.w])
  π.naturality i j f := by
    apply pullback.hom_ext
    · simp
    · simp only [Functor.const_obj_obj, Functor.const_obj_map, baseChangeIciDiagram_map,
        Category.id_comp, Category.assoc, pullback.lift_snd, pullback.lift_snd_assoc]
      rw [c.w]

lemma isPullback_baseChangeIciCone (H : IsPullback h b p (c.π.app (op l)))
    (i : (Set.Ici l)ᵒᵖ) :
    IsPullback ((baseChangeIciCone H).π.app i) b (pullback.snd p (D.map (homOfLE i.unop.2).op))
      (c.π.app (op i.unop.1)) := by
  refine IsPullback.of_right ?_ (pullback.lift_snd _ _ _) (IsPullback.of_hasPullback _ _)
  rw [baseChangeIciCone_π_app, pullback.lift_fst, c.w]
  exact H

/-- **Base change of a directed limit.** For a cartesian square `h : Y ⟶ Y₀`, `b : Y ⟶ lim Dᵢ`,
`p : Y₀ ⟶ Dₗ`, the scheme `Y` is the limit of the base changed system
`{ Y₀ ×_{Dₗ} Dᵢ }_{i ≥ l}`. -/
noncomputable def isLimitBaseChangeIciCone [IsDirectedOrder I] (hc : IsLimit c)
    (H : IsPullback h b p (c.π.app (op l))) : IsLimit (baseChangeIciCone H) :=
  have : IsConnected (Set.Ici l)ᵒᵖ := IsCofiltered.isConnected _
  isLimitOfIsPullbackOfIsConnected (baseChangeIciDiagramπ D l p) _
    (c.whisker (Subtype.mono_coe (· ∈ Set.Ici l)).functor.op)
    { hom := b
      w i := by simp [baseChangeIciCone] }
    (isPullback_baseChangeIciCone H)
    ((Functor.Initial.isLimitWhiskerEquiv _ c).symm hc)

end Directed

/-- The fibres of a base change: if `b'` is the base change of `b` along `g`, the fibre of `b'`
over `s` is the fibre of `b` over `s ≫ g`, so they have the same dimension. -/
lemma topologicalKrullDim_pullback_eq_of_isPullback {Y' Y S' S T : Scheme.{u}} {g' : Y' ⟶ Y}
    {b' : Y' ⟶ S'} {b : Y ⟶ S} {g : S' ⟶ S} (H : IsPullback g' b' b g) (s : T ⟶ S') :
    topologicalKrullDim (pullback b' s : Scheme.{u}) =
      topologicalKrullDim (pullback b (s ≫ g) : Scheme.{u}) := by
  let e := ((IsPullback.of_hasPullback b' s).paste_horiz H).isoPullback
  exact le_antisymm e.hom.isEmbedding.isInducing.topologicalKrullDim_le
    e.inv.isEmbedding.isInducing.topologicalKrullDim_le

section FGSubalgebra

variable (k : Type u) [Field k] (S : Scheme.{u}) [IsAffine S] [Algebra k Γ(S, ⊤)]

/-- The spectra of the finitely generated `k`-subalgebras of `Γ(S, ⊤)`. -/
noncomputable abbrev fgSubalgebraSpecDiagram :
    {A : Subalgebra k Γ(S, ⊤) // A.FG}ᵒᵖ ⥤ Scheme.{u} :=
  (CommRingCat.fgSubalgebraDiagramOf k Γ(S, ⊤)).op ⋙ Scheme.Spec

/-- The affine scheme `S` as a cone over the spectra of the finitely generated `k`-subalgebras
of `Γ(S, ⊤)`. -/
noncomputable def fgSubalgebraSpecCone : Cone (fgSubalgebraSpecDiagram k S) where
  pt := S
  π := (Functor.const _).map S.isoSpec.hom ≫
    (Scheme.Spec.mapCone (CommRingCat.fgSubalgebraCoconeOf k Γ(S, ⊤)).op).π

/-- An affine scheme `S` is the limit of the spectra of the finitely generated `k`-subalgebras of
`Γ(S, ⊤)`. -/
noncomputable def isLimitFGSubalgebraSpecCone : IsLimit (fgSubalgebraSpecCone k S) :=
  (isLimitOfPreserves Scheme.Spec (CommRingCat.isColimitFGSubalgebraCocone k Γ(S, ⊤)).op).ofIsoLimit
    (Cone.ext S.isoSpec.symm fun A ↦ by simp [fgSubalgebraSpecCone])

instance {i j : {A : Subalgebra k Γ(S, ⊤) // A.FG}ᵒᵖ} (f : i ⟶ j) :
    IsAffineHom ((fgSubalgebraSpecDiagram k S).map f) :=
  inferInstanceAs (IsAffineHom (Spec.map _))

instance (i : {A : Subalgebra k Γ(S, ⊤) // A.FG}ᵒᵖ) :
    CompactSpace ((fgSubalgebraSpecDiagram k S).obj i) :=
  inferInstanceAs (CompactSpace (Spec (.of i.unop.1)))

instance (i : {A : Subalgebra k Γ(S, ⊤) // A.FG}ᵒᵖ) :
    QuasiSeparatedSpace ((fgSubalgebraSpecDiagram k S).obj i) :=
  inferInstanceAs (QuasiSeparatedSpace (Spec (.of i.unop.1)))

/-- The structure morphism of the spectrum of a finitely generated `k`-subalgebra of `Γ(S, ⊤)`
to `Spec k`. -/
noncomputable def fgSubalgebraSpecToSpec (i : {A : Subalgebra k Γ(S, ⊤) // A.FG}ᵒᵖ) :
    (fgSubalgebraSpecDiagram k S).obj i ⟶ Spec (.of k) :=
  Spec.map (CommRingCat.ofHom (algebraMap k i.unop.1))

instance (i : {A : Subalgebra k Γ(S, ⊤) // A.FG}ᵒᵖ) :
    LocallyOfFiniteType (fgSubalgebraSpecToSpec k S i) := by
  have : Algebra.FiniteType k i.unop.1 := (Subalgebra.fg_iff_finiteType _).mp i.unop.2
  exact HasRingHomProperty.Spec_iff.mpr (RingHom.finiteType_algebraMap.mpr inferInstance)

instance (i : {A : Subalgebra k Γ(S, ⊤) // A.FG}ᵒᵖ) :
    QuasiCompact (fgSubalgebraSpecToSpec k S i) :=
  inferInstanceAs (QuasiCompact (Spec.map _))

end FGSubalgebra

/-- The `k`-algebra structure on the global sections of a scheme over `Spec k`. -/
noncomputable abbrev algebraΓOfHomSpec {k : Type u} [Field k] {S : Scheme.{u}}
    (aS : S ⟶ Spec (.of k)) : Algebra k Γ(S, ⊤) :=
  ((Scheme.ΓSpecIso (.of k)).inv ≫ aS.appTop).hom.toAlgebra

/-- **Fibre dimension of a proper morphism to an affine scheme over a field.** For a proper
morphism `b : Y ⟶ S` locally of finite presentation, with `S` affine over a field `k`, the
fibres of `b` over all points with values in fields have uniformly bounded dimension: `b` is the
base change of a proper morphism to a scheme of finite type over `k`. -/
lemma exists_topologicalKrullDim_pullback_le_of_isProper_of_isAffine {k : Type u} [Field k]
    {Y S : Scheme.{u}} [IsAffine S] (aS : S ⟶ Spec (.of k)) (b : Y ⟶ S) [IsProper b]
    [LocallyOfFinitePresentation b] :
    ∃ d : ℕ, ∀ (Ω : Type u) [Field Ω] (s : Spec (.of Ω) ⟶ S),
      topologicalKrullDim (pullback b s : Scheme.{u}) ≤ (d : WithBot ℕ∞) := by
  let := algebraΓOfHomSpec aS
  obtain ⟨i, Y₀, p, h, hp, -, H⟩ :=
    Scheme.exists_isProper_isPullback_of_isLimit (isLimitFGSubalgebraSpecCone k S) b
  obtain ⟨d, hd⟩ := exists_topologicalKrullDim_pullback_le (fgSubalgebraSpecToSpec k S (op i)) p
  refine ⟨d, fun Ω _ s ↦ ?_⟩
  rw [topologicalKrullDim_pullback_eq_of_isPullback H s]
  exact hd Ω _

/-- **Fibre dimension of a proper morphism to a Noetherian scheme over a field.** For a proper
morphism `b : Y ⟶ S` with `S` Noetherian over a field `k`, the fibres of `b` over all points
with values in fields have uniformly bounded dimension. This is checked on a finite affine open
cover of `S`, using
`AlgebraicGeometry.exists_topologicalKrullDim_pullback_le_of_isProper_of_isAffine`. -/
lemma exists_topologicalKrullDim_pullback_le_of_isProper_of_isNoetherian {k : Type u} [Field k]
    {Y S : Scheme.{u}} [IsNoetherian S] (aS : S ⟶ Spec (.of k)) (b : Y ⟶ S) [IsProper b] :
    ∃ d : ℕ, ∀ (Ω : Type u) [Field Ω] (s : Spec (.of Ω) ⟶ S),
      topologicalKrullDim (pullback b s : Scheme.{u}) ≤ (d : WithBot ℕ∞) := by
  have hU (U : S.affineOpens) : ∃ d : ℕ, ∀ (Ω : Type u) [Field Ω] (s : Spec (.of Ω) ⟶ U),
      topologicalKrullDim (pullback (b ∣_ U.1) s : Scheme.{u}) ≤ (d : WithBot ℕ∞) := by
    have : IsAffine U.1 := U.2
    exact exists_topologicalKrullDim_pullback_le_of_isProper_of_isAffine (U.1.ι ≫ aS) (b ∣_ U.1)
  choose d hd using hU
  obtain ⟨t, ht⟩ := isCompact_univ.elim_finite_subcover (fun U : S.affineOpens ↦ (U.1 : Set S))
    (fun U ↦ U.1.isOpen) (by
      rw [← TopologicalSpace.Opens.coe_iSup, iSup_affineOpens_eq_top,
        TopologicalSpace.Opens.coe_top])
  refine ⟨t.sup d, fun Ω _ s ↦ ?_⟩
  obtain ⟨U, hUt, hU⟩ := Set.mem_iUnion₂.mp (ht (Set.mem_univ (s.base default)))
  have hs : Set.range s.base ⊆ Set.range U.1.ι.base := by
    rintro _ ⟨x, rfl⟩
    rw [Subsingleton.elim x default, Scheme.Opens.range_ι]
    exact hU
  rw [← IsOpenImmersion.lift_fac U.1.ι s hs,
    ← topologicalKrullDim_pullback_eq_of_isPullback (isPullback_morphismRestrict b U.1).flip]
  exact (hd U Ω _).trans (by exact_mod_cast Finset.le_sup hUt)

end AlgebraicGeometry
