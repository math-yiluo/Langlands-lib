/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import Mathlib.AlgebraicGeometry.Sites.Fpqc
public import Mathlib.AlgebraicGeometry.Sites.Etale
public import Mathlib.CategoryTheory.Limits.Shapes.Pullback.IsPullback.Basic
public import Mathlib.CategoryTheory.Comma.StructuredArrow.Basic
public import Mathlib.CategoryTheory.ObjectProperty.FullSubcategory
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.PushforwardContinuous
public import WeilConjectures.CategoryTheory.SiteCoveringAxioms
public import Mathlib.CategoryTheory.Sites.PrecoverageToGrothendieck
public import Mathlib.CategoryTheory.Sites.SheafCohomology.Basic
public import WeilConjectures.CategoryTheory.RingedSiteModules
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.Abelian
import WeilConjectures.Mathlib.AlgebraicGeometry.Sites.Fpqc
import WeilConjectures.Algebra.Homology.CochainUniverseTransport.CochainCoefficientUniverseTransport

/-!
# Algebraic spaces, their small étale sites, and line modules

Source: Stacks Project, Tag 025Y; Properties of Spaces, Tags 03ED and 03G7;
Modules on Sites, Tags 0409 and 0B8Q (blueprint: def-trf-algebraic-space).

Representability is expressed by actual scheme-valued pullback squares of presheaves.
No presentation or atlas is chosen as part of the data of an algebraic space.
-/

@[expose] public section

universe u

open CategoryTheory CategoryTheory.Limits Opposite

namespace AlgebraicGeometry

namespace AlgebraicSpace

/-- Representability with a property of every scheme base change. The witness is a scheme
`U` over `S`, a projection `p : U ⟶ T`, and a pullback square representing `h_T ×_F G`.
Source: Stacks, Spaces, relative representable properties preceding Tag 025Y
(blueprint: def-trf-algebraic-space). -/
def IsRepresentableWith {S : Scheme.{u}}
    (P : MorphismProperty (Over S)) {G F : (Over S)ᵒᵖ ⥤ Type u} (f : G ⟶ F) : Prop :=
  ∀ (T : Over S) (a : yoneda.obj T ⟶ F),
    ∃ (U : Over S) (p : U ⟶ T) (q : yoneda.obj U ⟶ G),
      IsPullback q (yoneda.map p) f a ∧ P p

/-- A map of presheaves is representable if all its scheme base changes are schemes.
Source: Stacks, Spaces, Tag 025Y (blueprint: def-trf-algebraic-space). -/
def IsRepresentable {S : Scheme.{u}} {G F : (Over S)ᵒᵖ ⥤ Type u} (f : G ⟶ F) : Prop :=
  IsRepresentableWith ⊤ f

/-- A representable map is étale if its scheme base changes are étale.
Source: Stacks, Spaces, relative representable properties, Tag 025Y
(blueprint: def-trf-algebraic-space). -/
def IsEtale {S : Scheme.{u}} {G F : (Over S)ᵒᵖ ⥤ Type u} (f : G ⟶ F) : Prop :=
  IsRepresentableWith (fun _ _ p ↦ Etale p.left) f

/-- A representable map is surjective if its scheme base changes are surjective.
Source: Stacks, Spaces, relative representable properties, Tag 025Y
(blueprint: def-trf-algebraic-space). -/
def IsSurjective {S : Scheme.{u}} {G F : (Over S)ᵒᵖ ⥤ Type u} (f : G ⟶ F) : Prop :=
  IsRepresentableWith (fun _ _ p ↦ Surjective p.left) f

/-- The representable diagonal and existence of a surjective étale scheme atlas.
The fppf sheaf condition is supplied by the type of `F`.
Source: Stacks, Tag 025Y (blueprint: def-trf-algebraic-space). -/
def IsAlgebraicSpace {S : Scheme.{u}} (F : Sheaf (Scheme.fppfTopology.over S) (Type u)) :
    Prop :=
  IsRepresentable (prod.lift (𝟙 F.obj) (𝟙 F.obj)) ∧
    ∃ (U : Over S) (a : yoneda.obj U ⟶ F.obj), IsEtale a ∧ IsSurjective a

end AlgebraicSpace

/-- Algebraic spaces over `S`: fppf sheaves with representable diagonal and a surjective
étale scheme atlas. Morphisms are natural transformations, via the full subcategory.
Source: Stacks, Tag 025Y (blueprint: def-trf-algebraic-space). -/
abbrev AlgebraicSpace (S : Scheme.{u}) :=
  ObjectProperty.FullSubcategory (AlgebraicSpace.IsAlgebraicSpace (S := S))

namespace AlgebraicSpace

variable {S : Scheme.{u}}

/-- Composite representable étale maps are representable étale.
Source: Stacks, Spaces, relative representable properties preceding Tag 025Y
(blueprint: def-trf-algebraic-space).
Proof: base change the second map by a test scheme and represent its fibre product by a
scheme `V`. Base change the first map by `V` and represent that fibre product by `W`.
Pasting the two pullback squares gives the required representing square for the composite;
the scheme projection `W → V → T` is étale because both factors are étale. -/
theorem isEtale_comp {G H K : (Over S)ᵒᵖ ⥤ Type u} (f : G ⟶ H) (g : H ⟶ K)
    (hf : IsEtale f) (hg : IsEtale g) : IsEtale (f ≫ g) := by
  intro T a
  obtain ⟨V, p, q, hq, hp⟩ := hg T a
  obtain ⟨W, r, s, hs, hr⟩ := hf V q
  refine ⟨W, r ≫ p, s, ?_, ?_⟩
  · simpa only [Functor.map_comp] using hs.paste_vert hq
  · have := hp
    have := hr
    change Etale (r.left ≫ p.left)
    infer_instance

/-- The objects of the small étale site of `F` are schemes over `S` with representable
étale maps to `F`; morphisms are commuting triangles of natural transformations.
Source: Stacks, Properties of Spaces, Tag 03ED (blueprint: def-trf-algebraic-space). -/
abbrev EtaleSite (F : AlgebraicSpace S) :=
  ObjectProperty.FullSubcategory
    (fun T : CostructuredArrow yoneda F.obj.obj ↦ IsEtale T.hom)

/-- The underlying scheme of an object of the small étale site.
Source: Stacks, Tag 03ED (blueprint: def-trf-algebraic-space). -/
def etaleForget (F : AlgebraicSpace S) : F.EtaleSite ⥤ Scheme.{u} :=
  ObjectProperty.ι _ ⋙ CostructuredArrow.proj yoneda F.obj.obj ⋙ Over.forget S

/-- Covering presieves are jointly surjective families of étale scheme morphisms.
Source: Stacks, Tag 03ED (blueprint: def-trf-algebraic-space). -/
def etalePrecoverage (F : AlgebraicSpace S) : Precoverage F.EtaleSite where
  coverings T := {R |
    (∀ (U : F.EtaleSite) (f : U ⟶ T), R f → Etale ((etaleForget F).map f)) ∧
    ∀ x : (etaleForget F).obj T,
      ∃ (U : F.EtaleSite) (f : U ⟶ T), R f ∧
        ∃ y : (etaleForget F).obj U, ((etaleForget F).map f).base y = x}

/-- The topology generated by the jointly surjective étale coverings.
Source: Stacks, Tag 03ED (blueprint: def-trf-algebraic-space). -/
abbrev etaleTopology (F : AlgebraicSpace S) : GrothendieckTopology F.EtaleSite :=
  F.etalePrecoverage.toGrothendieck

private theorem isEtale_yoneda {U V : Over S} (r : U ⟶ V) (hr : Etale r.left) :
    IsEtale (yoneda.map r) := by
  intro T a
  let b : T ⟶ V := yoneda.preimage a
  refine ⟨Limits.pullback r b, Limits.pullback.snd r b,
    yoneda.map (Limits.pullback.fst r b), ?_, ?_⟩
  · have hb : yoneda.map b = a := yoneda.map_preimage a
    rw [← hb]
    exact (IsPullback.of_hasPullback r b).map yoneda
  · exact MorphismProperty.of_isPullback
      ((IsPullback.of_hasPullback r b).map (Over.forget S)) hr

private instance forget_faithful (F : AlgebraicSpace S) : F.etaleForget.Faithful := by
  unfold etaleForget
  infer_instance

private instance forget_reflects_pullbacks (F : AlgebraicSpace S) :
    ReflectsLimitsOfShape WalkingCospan (etaleForget F) := by
  unfold etaleForget
  infer_instance

private theorem covering_pullback {F : AlgebraicSpace S} {U V T : F.EtaleSite}
    (a : U ⟶ T) (b : V ⟶ T) (ha : Etale ((etaleForget F).map a)) :
    ∃ (W : F.EtaleSite) (p : W ⟶ U) (q : W ⟶ V),
      IsPullback p q a b ∧
        IsPullback ((etaleForget F).map p) ((etaleForget F).map q)
          ((etaleForget F).map a) ((etaleForget F).map b) := by
  let P := Limits.pullback a.hom.left b.hom.left
  let p : P ⟶ U.obj.left := Limits.pullback.fst _ _
  let q : P ⟶ V.obj.left := Limits.pullback.snd _ _
  have hq : Etale q.left := MorphismProperty.of_isPullback
    ((IsPullback.of_hasPullback a.hom.left b.hom.left).map (Over.forget S)) ha
  let W : F.EtaleSite := ⟨CostructuredArrow.mk (yoneda.map q ≫ V.obj.hom),
    isEtale_comp _ _ (isEtale_yoneda q hq) V.property⟩
  let p' : W ⟶ U := ObjectProperty.homMk (CostructuredArrow.homMk p (by
    dsimp [p, q, W]
    rw [← CostructuredArrow.w a.hom, ← CostructuredArrow.w b.hom,
      ← Category.assoc, ← Category.assoc,
      ← Functor.map_comp, ← Functor.map_comp, Limits.pullback.condition]))
  let q' : W ⟶ V := ObjectProperty.homMk (CostructuredArrow.homMk q (by rfl))
  have hpq : IsPullback ((etaleForget F).map p') ((etaleForget F).map q')
      ((etaleForget F).map a) ((etaleForget F).map b) :=
    (IsPullback.of_hasPullback a.hom.left b.hom.left).map (Over.forget S)
  refine ⟨W, p', q', ?_, hpq⟩
  exact hpq.of_map_of_faithful (etaleForget F)

private theorem precoverage_eq_comap (F : AlgebraicSpace S) :
    F.etalePrecoverage = Scheme.etalePrecoverage.comap F.etaleForget := by
  ext T R
  obtain ⟨I, U, a, rfl⟩ := R.exists_eq_ofArrows
  rw [Precoverage.mem_comap_iff, Presieve.map_ofArrows]
  change _ ↔ Presieve.ofArrows _ _ ∈ Scheme.precoverage (@Etale) _
  rw [Scheme.ofArrows_mem_precoverage_iff]
  constructor
  · intro h
    refine ⟨fun x ↦ ?_, fun i ↦ h.1 _ _ ⟨i⟩⟩
    obtain ⟨V, f, ⟨i⟩, y, hy⟩ := h.2 x
    exact ⟨i, y, hy⟩
  · intro h
    refine ⟨?_, fun x ↦ ?_⟩
    · rintro V f ⟨i⟩
      exact h.2 i
    · obtain ⟨i, y, hy⟩ := h.1 x
      exact ⟨U i, a i, ⟨i⟩, y, hy⟩

private theorem forget_preserves_covering_pullback {F : AlgebraicSpace S}
    {U V T : F.EtaleSite} (a : U ⟶ T) (b : V ⟶ T)
    (ha : Etale ((etaleForget F).map a)) :
    PreservesLimit (cospan a b) F.etaleForget := by
  obtain ⟨W, p, q, h, h'⟩ := covering_pullback a b ha
  exact h.preservesLimit_cospan_iff.mpr h'

private instance etalePrecoverage_hasPullbacks (F : AlgebraicSpace S) :
    F.etalePrecoverage.HasPullbacks where
  hasPullbacks_of_mem b hR := ⟨fun ha ↦ by
    obtain ⟨W, p, q, h, _⟩ := covering_pullback _ b (hR.1 _ _ ha)
    exact h.hasPullback⟩

private instance etaleForget_preserves_coveringPullbacks (F : AlgebraicSpace S) :
    F.etalePrecoverage.PullbacksPreservedBy F.etaleForget where
  preservesPairwisePullbacks_of_mem {_X _R} hR :=
    ⟨fun {_U _V _a _b} ha _ ↦
      forget_preserves_covering_pullback _ _ (hR.1 _ _ ha)⟩

private instance scheme_etalePrecoverage_isStableUnderBaseChange :
    Scheme.etalePrecoverage.{u}.IsStableUnderBaseChange := by
  unfold Scheme.etalePrecoverage
  infer_instance

private instance etalePrecoverage_isStableUnderBaseChange (F : AlgebraicSpace S) :
    F.etalePrecoverage.IsStableUnderBaseChange where
  mem_coverings_of_isPullback {ι} {T} {U} a ha {V} b {W} p q h := by
    rw [precoverage_eq_comap, Precoverage.mem_comap_iff, Presieve.map_ofArrows]
    have ha' := ha
    rw [precoverage_eq_comap, Precoverage.mem_comap_iff, Presieve.map_ofArrows] at ha'
    apply Precoverage.mem_coverings_of_isPullback _ ha' (F.etaleForget.map b)
      (fun i ↦ F.etaleForget.map (p i)) (fun i ↦ F.etaleForget.map (q i))
    intro i
    have := forget_preserves_covering_pullback (a i) b (ha.1 _ _ ⟨i⟩)
    have := preservesPullback_symmetry F.etaleForget (a i) b
    exact (h i).map F.etaleForget

private theorem etaleForget_isContinuous (F : AlgebraicSpace S) :
    F.etaleForget.IsContinuous F.etaleTopology Scheme.etaleTopology := by
  apply Functor.isContinuous_toGrothendieck_of_pullbacksPreservedBy
  exact (precoverage_eq_comap F).le

/-- The structure presheaf has value `Γ(T, O_T)` and the usual restriction maps.
Source: Stacks, Tag 03G7 (blueprint: def-trf-algebraic-space). -/
def structurePresheaf (F : AlgebraicSpace S) : F.EtaleSiteᵒᵖ ⥤ RingCat.{u} :=
  (etaleForget F).op ⋙ Scheme.Γ ⋙ forget₂ CommRingCat RingCat

/-- The structure presheaf is a sheaf.
Source: Stacks, Properties of Spaces, lemma-sheaf-condition-holds preceding Tag 03G7
(blueprint: def-trf-algebraic-space).
Proof: an étale covering of an object of the small site is a jointly surjective étale
cover of its underlying scheme. The usual descent equalizer for regular functions on
that cover is the sheaf equalizer for this presheaf. The same holds for every generated
covering sieve, by the sheaf criterion for a generating precoverage. -/
theorem structurePresheaf_isSheaf (F : AlgebraicSpace S) :
    Presheaf.IsSheaf F.etaleTopology F.structurePresheaf := by
  have := etaleForget_isContinuous F
  exact GrothendieckTopology.HasSheafCompose.isSheaf
    (F := forget₂ CommRingCat RingCat) (F.etaleForget.op ⋙ Scheme.Γ)
    (Functor.op_comp_isSheaf_of_isSheaf F.etaleForget _ _ _
      (Scheme.isSheaf_Γ Scheme.etaleTopology))

/-- The structure sheaf: its data are the explicit global-sections presheaf; only the
sheaf-condition proof is postponed in the preceding named theorem.
Source: Stacks, Tag 03G7 (blueprint: def-trf-algebraic-space). -/
def structureSheaf (F : AlgebraicSpace S) : Sheaf F.etaleTopology RingCat.{u} :=
  ⟨F.structurePresheaf, F.structurePresheaf_isSheaf⟩

/-- Sheaves of modules over the structure sheaf on the small étale site.
Source: Stacks, Tags 03G7 and 0409 (blueprint: def-trf-algebraic-space). -/
abbrev Modules (F : AlgebraicSpace S) :=
  ringedSiteModules.{u} F.structureSheaf

/-- An étale map induces the inclusion of small étale sites by composition of maps.
It leaves underlying schemes and scheme morphisms unchanged.
Source: Stacks, Properties of Spaces, Tag 03ED and the restriction after Tag 03G7
(blueprint: def-trf-algebraic-space). -/
def etaleMap {G F : AlgebraicSpace S} (f : G ⟶ F) (hf : IsEtale f.hom.hom) :
    G.EtaleSite ⥤ F.EtaleSite :=
  ObjectProperty.lift _
    (ObjectProperty.ι _ ⋙ CostructuredArrow.map f.hom.hom)
    (fun T ↦ isEtale_comp T.obj.hom f.hom.hom T.property hf)

/-- Inclusion of small étale sites along an étale map is continuous.
Source: Stacks, Properties of Spaces, Tag 03ED and the restriction after Tag 03G7
(blueprint: def-trf-algebraic-space).
Proof: a covering family is unchanged on underlying schemes, so is still jointly
surjective and étale. Pullback squares in the source small site are scheme pullback
squares, and composition with the given map leaves those squares unchanged. Thus the
covering equalizers for a sheaf restrict to covering equalizers on the source site. -/
theorem etaleMap_isContinuous {G F : AlgebraicSpace S} (f : G ⟶ F)
    (hf : IsEtale f.hom.hom) :
    Functor.IsContinuous (etaleMap f hf) G.etaleTopology F.etaleTopology := by
  have : G.etalePrecoverage.PullbacksPreservedBy (etaleMap f hf) := by
    constructor
    intro T R hR
    constructor
    intro U V a b ha hb
    have : PreservesLimit (cospan a b) G.etaleForget :=
      forget_preserves_covering_pullback a b (hR.1 _ _ ha)
    have : PreservesLimit (cospan a b) (etaleMap f hf ⋙ F.etaleForget) := this
    exact preservesLimit_of_reflects_of_preserves (etaleMap f hf) F.etaleForget
  apply Functor.isContinuous_toGrothendieck_of_pullbacksPreservedBy
  intro T R hR
  rw [Precoverage.mem_comap_iff]
  obtain ⟨I, U, a, rfl⟩ := R.exists_eq_ofArrows
  rw [Presieve.map_ofArrows, precoverage_eq_comap, Precoverage.mem_comap_iff,
    Presieve.map_ofArrows]
  change Presieve.ofArrows (fun i ↦ G.etaleForget.obj (U i))
    (fun i ↦ G.etaleForget.map (a i)) ∈ Scheme.etalePrecoverage _
  rwa [precoverage_eq_comap, Precoverage.mem_comap_iff, Presieve.map_ofArrows] at hR

/-- Pullback of modules along an étale map is precomposition on the small étale sites.
The ring map is the identity on the regular functions of each underlying scheme.
Source: Stacks, Properties of Spaces, restriction of the structure sheaf after Tag 03G7
(blueprint: def-trf-algebraic-space). -/
noncomputable def pullback {G F : AlgebraicSpace S} (f : G ⟶ F)
    (hf : IsEtale f.hom.hom) : F.Modules ⥤ G.Modules :=
  letI := etaleMap_isContinuous f hf
  SheafOfModules.pushforward (F := etaleMap f hf) ⟨𝟙 _⟩

/-- Pullback to an étale object is restriction to its localized étale site.
Source: Stacks, Properties of Spaces, restriction of the structure sheaf after Tag 03G7
(blueprint: def-trf-algebraic-space). -/
noncomputable def etalePullback (F : AlgebraicSpace S) (T : F.EtaleSite) :=
  SheafOfModules.overFunctor F.structureSheaf T

/-- A line module is locally isomorphic to the structure sheaf. Such modules are called
invertible here; on this locally ringed site this agrees with tensor invertibility.
Source: Stacks, Modules on Sites, Tags 0409 and 0B8Q
(blueprint: def-trf-algebraic-space). -/
def IsLineModule (F : AlgebraicSpace S) (M : F.Modules) : Prop :=
  ∀ T : F.EtaleSite, ∃ R : Sieve T, R ∈ F.etaleTopology T ∧
    ∀ (U : F.EtaleSite) (f : U ⟶ T), R f →
      Nonempty ((F.etalePullback U).obj M ≅ SheafOfModules.unit (F.structureSheaf.over U))

end AlgebraicSpace

end AlgebraicGeometry
