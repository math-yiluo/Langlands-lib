/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.CompExact
public import WeilConjectures.CategoryTheory.GrothendieckAbelian.HasDerivedCategory
public import WeilConjectures.AlgebraicGeometry.Sites.LerayVanishing
public import WeilConjectures.AlgebraicGeometry.Sites.ZariskiSite
public import WeilConjectures.Mathlib.CategoryTheory.Functor.Flat
public import WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.LowerShriek.Open.Injective

/-!
# Comparison of the étale and the Zariski site

For a scheme `X`, restricting étale sheaves to the open subschemes of `X` defines the direct
image `ε_*` from abelian étale sheaves to abelian Zariski sheaves
(`AlgebraicGeometry.Scheme.etaleToZariski`). Since abelian étale sheaves take values in
`AddCommGrpCat.{u + 1}`, the Zariski side is the site of open subsets of the underlying space of
`X` lifted to the universe `u + 1` (`AlgebraicGeometry.Scheme.zariskiSpace`), so that the results
on sheaves on topological spaces, which are stated in a single universe, apply to it.

The functor `ε_*` is the pushforward along the representably flat, continuous functor
`AlgebraicGeometry.Scheme.opensToEtale`; hence it has an exact left adjoint `ε⁻¹` and preserves
injective objects. The Grothendieck spectral sequence `Hᵖ(X_Zar, Rᵠε_* F) ⟹ Hᵖ⁺ᵠ(X_ét, F)` then
gives

- `AlgebraicGeometry.Scheme.subsingleton_H_of_isZero_rightDerived_etaleToZariski`: for `X`
  noetherian of dimension at most `d`, if `Rᵠε_* F = 0` for `q > e`, then `Hⁿ(X_ét, F) = 0` for
  `n > d + e` (Grothendieck vanishing on the Zariski side);
- `AlgebraicGeometry.Scheme.isZero_rightDerived_etaleToZariski_of_subsingleton_H`: the sheaf
  `Rᵠε_* F` vanishes as soon as `Hᵠ(V_ét, F|_V) = 0` for every affine open `V`, being the
  sheafification of the presheaf `V ↦ Hᵠ(V_ét, F|_V)`.
-/

@[expose] public section

universe w u

open CategoryTheory Limits Opposite TopologicalSpace

namespace CategoryTheory.Functor

variable {C D E : Type*} [Category* C] [Category* D] [Category* E] [Abelian C] [Abelian D]
  [Abelian E] [HasInjectiveResolutions C]

/-- The right derived functors of a composite `G ⋙ H` with an exact functor `H` are obtained by
applying `H` to those of `G`: `Rⁿ(G ⋙ H) X ≅ H (Rⁿ G X)`. -/
noncomputable def rightDerivedCompObjIsoOfExact (G : C ⥤ D) (H : D ⥤ E) [G.Additive]
    [H.Additive] [PreservesFiniteLimits H] [PreservesFiniteColimits H] (X : C) (n : ℕ) :
    ((G ⋙ H).rightDerived n).obj X ≅ H.obj ((G.rightDerived n).obj X) :=
  have : H.PreservesHomology := {}
  (injectiveResolution X).isoRightDerivedObj (G ⋙ H) n ≪≫
    (((G.mapHomologicalComplex _).obj (injectiveResolution X).cocomplex).sc n).mapHomologyIso H ≪≫
    H.mapIso ((injectiveResolution X).isoRightDerivedObj G n).symm

end CategoryTheory.Functor

namespace TopCat

/-- The sheafification of an abelian presheaf `P` on a topological space vanishes as soon as
every point of every open `U` has an open neighbourhood `W ⊆ U` with `P(W) = 0`. -/
lemma isZero_presheafToSheaf_of_forall_exists {T : TopCat.{w}}
    (P : (TopologicalSpace.Opens T)ᵒᵖ ⥤ AddCommGrpCat.{w})
    (hP : ∀ (U : TopologicalSpace.Opens T) (x : T), x ∈ U →
      ∃ W : TopologicalSpace.Opens T, W ≤ U ∧ x ∈ W ∧ Subsingleton (P.obj (op W))) :
    IsZero ((presheafToSheaf (Opens.grothendieckTopology T) AddCommGrpCat.{w}).obj P) := by
  let J := Opens.grothendieckTopology T
  let S := (presheafToSheaf J AddCommGrpCat.{w}).obj P
  let ST := (sheafCompose J (CategoryTheory.forget AddCommGrpCat.{w})).obj S
  have h (U : TopologicalSpace.Opens T) (s : S.obj.obj (op U)) : s = 0 := by
    let R : Sieve U :=
      { arrows := fun _ f ↦ S.obj.map f.op s = 0
        downward_closed := fun {_ _} f hf g ↦ by
          rw [op_comp, S.obj.map_comp, ConcreteCategory.comp_apply, hf, map_zero] }
    have hR : R ∈ J U := by
      intro x hx
      obtain ⟨V, f, ⟨t, ht⟩, hxV⟩ := Presheaf.imageSieve_mem J (toSheafify J P) s x hx
      obtain ⟨W, hWV, hxW, hW⟩ := hP V x hxV
      refine ⟨W, homOfLE hWV ≫ f, ?_, hxW⟩
      change S.obj.map (homOfLE hWV ≫ f).op s = 0
      rw [op_comp, S.obj.map_comp, ConcreteCategory.comp_apply, ← ht,
        ← NatTrans.naturality_apply, Subsingleton.elim (P.map _ t) 0, map_zero]
    refine ((isSheaf_iff_isSheaf_of_type _ _).1 ST.property _ hR).isSeparatedFor.ext
      fun V f hf ↦ ?_
    change S.obj.map f.op s = S.obj.map f.op 0
    rw [map_zero]
    exact hf
  rw [IsZero.iff_id_eq_zero]
  ext U x
  exact h U.unop x

end TopCat

namespace AlgebraicGeometry.Scheme

variable (X : Scheme.{u})

/-- The underlying topological space of `X`, lifted to the universe `u + 1`, so that abelian
sheaves with values in `AddCommGrpCat.{u + 1}` on it fall under the results on sheaves on
topological spaces in a single universe. -/
abbrev zariskiSpace : TopCat.{u + 1} := TopCat.of (ULift.{u + 1} X)

variable {X}

/-- The open subscheme of `X` corresponding to an open subset of `X.zariskiSpace`. -/
def zariskiSpaceOpens (V : TopologicalSpace.Opens X.zariskiSpace) : X.Opens :=
  Homeomorph.ulift.opensCongr V

/-- Membership in the open subscheme corresponding to an open subset of `X.zariskiSpace`. -/
lemma mem_zariskiSpaceOpens {V : TopologicalSpace.Opens X.zariskiSpace} {x : X} :
    x ∈ zariskiSpaceOpens V ↔ ULift.up x ∈ V :=
  Iff.rfl


/-- The correspondence between opens of `X.zariskiSpace` and of `X` is monotone. -/
lemma zariskiSpaceOpens_mono {V W : TopologicalSpace.Opens X.zariskiSpace} (h : V ≤ W) :
    zariskiSpaceOpens V ≤ zariskiSpaceOpens W :=
  (Homeomorph.ulift.opensCongr).monotone h

/-- The open subscheme `U` of `X` as an object of the small étale site of `X`. -/
noncomputable abbrev opensEtale (U : X.Opens) : X.Etale :=
  MorphismProperty.Over.mk ⊤ U.ι inferInstance

/-- There is at most one morphism to an open subscheme in the small étale site. -/
lemma opensEtale_hom_ext {A : X.Etale} {U : X.Opens} (f g : A ⟶ opensEtale U) : f = g :=
  MorphismProperty.Over.Hom.ext (by
    rw [← cancel_mono U.ι]
    exact (MorphismProperty.Over.w f).trans (MorphismProperty.Over.w g).symm)

/-- An object `A` of the small étale site maps to the open subscheme `U` if its image lies in
`U`. -/
noncomputable def opensEtaleLift {A : X.Etale} {U : X.Opens} (h : ∀ a, A.hom a ∈ U) :
    A ⟶ opensEtale U :=
  MorphismProperty.Over.homMk (IsOpenImmersion.lift U.ι A.hom (by
    rintro _ ⟨a, rfl⟩
    exact (congrArg (A.hom a ∈ ·) (Opens.range_ι U)).mpr (h a)))
    (IsOpenImmersion.lift_fac _ _ _) trivial

/-- The image of an object of the small étale site mapping to an open subscheme `U` lies in
`U`. -/
lemma mem_of_hom_opensEtale {A : X.Etale} {U : X.Opens} (f : A ⟶ opensEtale U) :
    ∀ a, A.hom a ∈ U := by
  intro a
  rw [← MorphismProperty.Over.w f]
  change U.ι (f.left a) ∈ U
  simp

variable (X) in
/-- The functor from the Zariski site (on the lifted space) to the small étale site, sending
an open subset to the corresponding open subscheme. -/
@[simps]
noncomputable def opensToEtale : TopologicalSpace.Opens X.zariskiSpace ⥤ X.Etale where
  obj V := opensEtale (zariskiSpaceOpens V)
  map f := MorphismProperty.Over.homMk (X.homOfLE (zariskiSpaceOpens_mono f.le))
    (X.homOfLE_ι _) trivial
  map_id _ := opensEtale_hom_ext _ _
  map_comp _ _ := opensEtale_hom_ext _ _

/-- The functor `opensToEtale` is representably flat: an étale `X`-scheme maps to an open
subscheme `U` (uniquely) if and only if its image lies in `U`, and these opens are stable under
finite intersections. -/
instance : RepresentablyFlat (opensToEtale X) := by
  constructor
  intro A
  refine @IsCofiltered.mk _ _ ?_ ?_
  · constructor
    · intro V W
      have h : ∀ a, A.hom a ∈ zariskiSpaceOpens (V.right ⊓ W.right) := fun a ↦
        ⟨mem_of_hom_opensEtale V.hom a, mem_of_hom_opensEtale W.hom a⟩
      exact ⟨StructuredArrow.mk (Y := V.right ⊓ W.right) (opensEtaleLift h),
        StructuredArrow.homMk (homOfLE inf_le_left) (opensEtale_hom_ext _ _),
        StructuredArrow.homMk (homOfLE inf_le_right) (opensEtale_hom_ext _ _), trivial⟩
    · exact fun _ _ _ _ ↦ ⟨_, 𝟙 _, by ext; exact Subsingleton.elim _ _⟩
  · exact ⟨StructuredArrow.mk (Y := ⊤) (opensEtaleLift (fun _ ↦ trivial))⟩

/-- The functor `opensToEtale` sends Zariski coverings to étale coverings. -/
lemma coverPreserving_opensToEtale :
    CoverPreserving (Opens.grothendieckTopology X.zariskiSpace) X.smallEtaleTopology
      (opensToEtale X) where
  cover_preserve {V S} hS := by
    let ι := Σ W : TopologicalSpace.Opens X.zariskiSpace, {g : W ⟶ V // S g}
    refine X.smallEtaleTopology.superset_covering ?_
      ((ofArrows_mem_smallEtaleTopology_iff (fun i : ι ↦ (opensToEtale X).map i.2.1)).2 ?_)
    · exact (Sieve.generate_le_iff _ _).2
        (Presieve.ofArrows_le_iff.2 fun i ↦ Sieve.image_mem_functorPushforward _ _ i.2.2)
    · ext y
      simp only [Set.mem_iUnion, Set.mem_range, Set.mem_univ, iff_true]
      obtain ⟨W, g, hg, hy⟩ := hS (ULift.up y.1) y.2
      exact ⟨⟨W, g, hg⟩, ⟨y.1, hy⟩, Subtype.ext (X.homOfLE_apply (zariskiSpaceOpens_mono g.le) _)⟩

/-- The functor `opensToEtale` is continuous: it is representably flat and cover preserving. -/
instance : (opensToEtale X).IsContinuous (Opens.grothendieckTopology X.zariskiSpace)
    X.smallEtaleTopology :=
  Functor.isContinuous_of_coverPreserving (compatiblePreservingOfFlat _ _)
    coverPreserving_opensToEtale

/-- Pointwise left Kan extensions along `(opensToEtale X).op` exist, the indexing comma
categories being essentially `u + 1`-small. -/
instance (G : (TopologicalSpace.Opens X.zariskiSpace)ᵒᵖ ⥤ AddCommGrpCat.{u + 1}) :
    (opensToEtale X).op.HasPointwiseLeftKanExtension G := fun V ↦ by
  have : HasColimitsOfShape (CostructuredArrow (opensToEtale X).op V) AddCommGrpCat.{u + 1} :=
    hasColimitsOfShape_of_essentiallySmall.{u + 1} _ _
  infer_instance

variable (X) in
/-- The direct image `ε_*` from abelian étale sheaves to abelian Zariski sheaves (on the lifted
underlying space), restricting an étale sheaf to the open subschemes. -/
noncomputable abbrev etaleToZariski :
    Sheaf X.smallEtaleTopology AddCommGrpCat.{u + 1} ⥤
      Sheaf (Opens.grothendieckTopology X.zariskiSpace) AddCommGrpCat.{u + 1} :=
  (opensToEtale X).sheafPushforwardContinuous _ _ _

/-- The direct image `ε_*` is additive. -/
instance : (etaleToZariski X).Additive where

variable (X) in
/-- The inverse image `ε⁻¹` from abelian Zariski sheaves to abelian étale sheaves, the left
adjoint of `ε_*`. -/
noncomputable abbrev zariskiToEtale :
    Sheaf (Opens.grothendieckTopology X.zariskiSpace) AddCommGrpCat.{u + 1} ⥤
      Sheaf X.smallEtaleTopology AddCommGrpCat.{u + 1} :=
  Functor.sheafPullbackConstruction.sheafPullback (opensToEtale X) _ _ _

variable (X) in
/-- The adjunction `ε⁻¹ ⊣ ε_*`. -/
noncomputable def zariskiToEtaleAdjunction : zariskiToEtale X ⊣ etaleToZariski X :=
  Functor.sheafPullbackConstruction.sheafAdjunctionContinuous _ _ _ _

variable (X) in
/-- The whole scheme `X` is a terminal object of its small étale site. -/
noncomputable def isTerminalOpensToEtaleTop : IsTerminal ((opensToEtale X).obj ⊤) :=
  IsTerminal.ofUniqueHom (fun _ ↦ opensEtaleLift (fun _ ↦ trivial))
    (fun _ _ ↦ opensEtale_hom_ext _ _)

variable (X) in
/-- The global sections of `ε_* F` are the global sections of `F`. -/
noncomputable def etaleToZariskiCompSectionsIso :
    etaleToZariski X ⋙ Sheaf.sectionsFunctorAt (Opens.grothendieckTopology X.zariskiSpace) ⊤ ≅
      Sheaf.sectionsFunctorAt X.smallEtaleTopology (⊤_ X.Etale) :=
  NatIso.ofComponents (fun F ↦ F.obj.mapIso
    (terminalIsTerminal.conePointUniqueUpToIso (isTerminalOpensToEtaleTop X)).op)
    (fun φ ↦ (φ.hom.naturality _).symm)

/-- **Leray vanishing for the comparison of the étale and the Zariski site.** Let `X` be a
noetherian scheme of dimension at most `d` and `F` an abelian étale sheaf on `X` such that
`Rᵠε_* F = 0` for `q > e`. Then `Hⁿ(X_ét, F) = 0` for `n > d + e`: the spectral sequence
`Hᵖ(X_Zar, Rᵠε_* F) ⟹ Hᵖ⁺ᵠ(X_ét, F)` has nonzero terms only for `p ≤ d` (Grothendieck
vanishing) and `q ≤ e`. -/
theorem subsingleton_H_of_isZero_rightDerived_etaleToZariski [IsNoetherian X] {d e : ℕ}
    (hX : topologicalKrullDim X ≤ (d : WithBot ℕ∞))
    (F : Sheaf X.smallEtaleTopology AddCommGrpCat.{u + 1})
    (hF : ∀ q : ℕ, e < q → IsZero (((etaleToZariski X).rightDerived q).obj F))
    (n : ℕ) (hn : d + e < n) : Subsingleton (Sheaf.H F n) := by
  rw [Etale.subsingleton_H_iff_isZero_rightDerived_Γ]
  have : (Sheaf.sectionsFunctorAt (Opens.grothendieckTopology X.zariskiSpace)
      (⊤ : TopologicalSpace.Opens X.zariskiSpace)).Additive :=
    inferInstanceAs
      (sheafToPresheaf _ _ ⋙ (CategoryTheory.evaluation _ AddCommGrpCat.{u + 1}).obj _).Additive
  have hFG := (zariskiToEtaleAdjunction X).isAcyclicComposablePair
    (Sheaf.sectionsFunctorAt (Opens.grothendieckTopology X.zariskiSpace)
      (⊤ : TopologicalSpace.Opens X.zariskiSpace))
  have : NoetherianSpace X.zariskiSpace :=
    (noetherianSpace_iff_of_homeomorph Homeomorph.ulift.symm).1 inferInstance
  have : QuasiSober X.zariskiSpace := Homeomorph.ulift.isOpenEmbedding.quasiSober
  have hdim : topologicalKrullDim X.zariskiSpace = topologicalKrullDim X :=
    IsHomeomorph.topologicalKrullDim_eq _ Homeomorph.ulift.isHomeomorph
  refine IsZero.of_iso (Functor.isZero_rightDerived_comp_of_lt_add _ _ hFG F hF
    (fun p q hp ↦ (Sheaf.subsingleton_H_iff_isZero_rightDerived
      (Opens.grothendieckTopology X.zariskiSpace) isTerminalTop p _).1
      (TopCat.Sheaf.subsingleton_H_of_topologicalKrullDim_lt (X := X.zariskiSpace) _
        (by rw [hdim]; exact hX.trans_lt (by exact_mod_cast hp)))) n hn)
    ((NatIso.rightDerived (etaleToZariskiCompSectionsIso X) n).app F).symm

/-- **The higher direct images `Rᵠε_* F` vanish if the cohomology over affine opens does.** The
sheaf `Rᵠε_* F` is the sheafification of the presheaf `V ↦ Hᵠ(V_ét, F|_V)`, and the affine opens
form a basis of the topology of `X`. -/
lemma isZero_rightDerived_etaleToZariski_of_forall_isAffineOpen
    (F : Sheaf X.smallEtaleTopology AddCommGrpCat.{u + 1}) (q : ℕ)
    (h : ∀ V : TopologicalSpace.Opens X.zariskiSpace, IsAffineOpen (zariskiSpaceOpens V) →
      IsZero ((((Sheaf.sectionsFunctorAt X.smallEtaleTopology ((opensToEtale X).obj V) :
        Sheaf _ AddCommGrpCat.{u + 1} ⥤ _)).rightDerived q).obj F)) :
    IsZero (((etaleToZariski X).rightDerived q).obj F) := by
  let J := Opens.grothendieckTopology X.zariskiSpace
  let P := etaleToZariski X ⋙ sheafToPresheaf J AddCommGrpCat.{u + 1}
  let e : etaleToZariski X ≅ P ⋙ presheafToSheaf J AddCommGrpCat.{u + 1} :=
    (Functor.rightUnitor _).symm ≪≫
      Functor.isoWhiskerLeft _
        (asIso (sheafificationAdjunction J AddCommGrpCat.{u + 1}).counit).symm ≪≫
      (Functor.associator _ _ _).symm
  have : P.Additive := inferInstanceAs (etaleToZariski X ⋙ _).Additive
  refine IsZero.of_iso ?_ ((NatIso.rightDerived e q).app F ≪≫
    Functor.rightDerivedCompObjIsoOfExact P _ F q)
  refine TopCat.isZero_presheafToSheaf_of_forall_exists _ fun U x hx ↦ ?_
  obtain ⟨W, hW, hxW, hWU⟩ := (TopologicalSpace.Opens.isBasis_iff_nbhd.1 X.isBasis_affineOpens)
    (show x.down ∈ zariskiSpaceOpens U from hx)
  let V : TopologicalSpace.Opens X.zariskiSpace := Homeomorph.ulift.opensCongr.symm W
  have hV : zariskiSpaceOpens V = W := Homeomorph.ulift.opensCongr.apply_symm_apply W
  refine ⟨V, fun y hy ↦ hWU (show y.down ∈ W from hy), hxW, ?_⟩
  rw [← AddCommGrpCat.isZero_iff_subsingleton]
  have eV : P ⋙ (CategoryTheory.evaluation _ AddCommGrpCat.{u + 1}).obj (op V) ≅
      Sheaf.sectionsFunctorAt X.smallEtaleTopology ((opensToEtale X).obj V) :=
    NatIso.ofComponents (fun _ ↦ Iso.refl _)
  refine IsZero.of_iso ?_ ((Functor.rightDerivedCompObjIsoOfExact P
    ((CategoryTheory.evaluation _ AddCommGrpCat.{u + 1}).obj (op V)) F q).symm ≪≫
    (NatIso.rightDerived eV q).app F)
  exact h V (by rw [hV]; exact hW)

variable (X) in
/-- The scheme `X` itself, as a terminal object of its small étale site. -/
noncomputable def isTerminalEtaleMkId :
    IsTerminal (MorphismProperty.Over.mk ⊤ (𝟙 X) (MorphismProperty.id_mem _ X) : X.Etale) :=
  IsTerminal.ofUniqueHom (fun A ↦ MorphismProperty.Over.homMk A.hom (Category.comp_id _) trivial)
    (fun _ f ↦ MorphismProperty.Over.Hom.ext
      ((Category.comp_id _).symm.trans (MorphismProperty.Over.w f)))

/-- **Derived sections over an open subscheme.** For an open subscheme `U` of `X` and an abelian
étale sheaf `F` on `X`, the derived sections of `F` over `U` are the étale cohomology of the
restriction `F|_U`: if `Hᵠ(U_ét, F|_U) = 0`, then `Rᵠ Γ(U, -)(F) = 0`. -/
lemma isZero_rightDerived_sectionsFunctorAt_opensEtale (U : X.Opens)
    (F : Sheaf X.smallEtaleTopology AddCommGrpCat.{u + 1}) (q : ℕ)
    (h : Subsingleton (Sheaf.H ((Etale.upperStar AddCommGrpCat.{u + 1} U.ι).obj F) q)) :
    IsZero ((((Sheaf.sectionsFunctorAt X.smallEtaleTopology (opensEtale U) :
      Sheaf _ AddCommGrpCat.{u + 1} ⥤ _)).rightDerived q).obj F) := by
  let := HasDerivedCategory.standard (Sheaf X.smallEtaleTopology AddCommGrpCat.{u + 1})
  let := HasDerivedCategory.standard (Sheaf U.toScheme.smallEtaleTopology AddCommGrpCat.{u + 1})
  let := HasDerivedCategory.standard AddCommGrpCat.{u + 1}
  have hU : Etale U.ι := inferInstance
  let j := Etale.localizationRestriction AddCommGrpCat.{u + 1} U.ι hU
  let b : U.toScheme.Etale :=
    MorphismProperty.Over.mk ⊤ (𝟙 U.toScheme) (MorphismProperty.id_mem _ _)
  let ΓU : Sheaf U.toScheme.smallEtaleTopology AddCommGrpCat.{u + 1} ⥤ AddCommGrpCat.{u + 1} :=
    Sheaf.sectionsFunctorAt _ b
  let e : (MorphismProperty.Over.map ⊤ hU).obj b ≅ opensEtale U :=
    MorphismProperty.Over.isoMk (Iso.refl _) (by
      simp only [Iso.refl_hom, Category.id_comp]
      exact (Category.id_comp _).symm)
  let eΓ : (Sheaf.sectionsFunctorAt X.smallEtaleTopology (opensEtale U) :
      Sheaf _ AddCommGrpCat.{u + 1} ⥤ _) ≅ j ⋙ ΓU :=
    NatIso.ofComponents (fun G ↦ G.obj.mapIso e.op) (fun φ ↦ (φ.hom.naturality e.op.hom).symm)
  have : j.Additive := { }
  have : PreservesFiniteColimits j :=
    preservesFiniteColimits_of_natIso
      (Etale.upperStarIsoLocalizationRestriction AddCommGrpCat.{u + 1} U.ι hU)
  have : PreservesFiniteLimits j :=
    preservesFiniteLimits_of_natIso
      (Etale.upperStarIsoLocalizationRestriction AddCommGrpCat.{u + 1} U.ι hU)
  refine IsZero.of_iso ?_ ((NatIso.rightDerived eΓ q).app F ≪≫
    (Functor.rightDerivedCompIsoOfExact j ΓU q).app F)
  refine IsZero.of_iso ?_ (ΓU.rightDerived q |>.mapIso
    ((Etale.upperStarIsoLocalizationRestriction AddCommGrpCat.{u + 1} U.ι hU).app F).symm)
  exact (Sheaf.subsingleton_H_iff_isZero_rightDerived U.toScheme.smallEtaleTopology
    (isTerminalEtaleMkId U.toScheme) q _).1 h

/-- **The higher direct images `Rᵠε_* F` vanish if the cohomology of affine opens does.** If
`Hᵠ(V_ét, F|_V) = 0` for every affine open `V` of `X`, then `Rᵠε_* F = 0`. -/
lemma isZero_rightDerived_etaleToZariski_of_subsingleton_H
    (F : Sheaf X.smallEtaleTopology AddCommGrpCat.{u + 1}) (q : ℕ)
    (h : ∀ U : X.Opens, IsAffineOpen U →
      Subsingleton (Sheaf.H ((Etale.upperStar AddCommGrpCat.{u + 1} U.ι).obj F) q)) :
    IsZero (((etaleToZariski X).rightDerived q).obj F) :=
  isZero_rightDerived_etaleToZariski_of_forall_isAffineOpen F q fun _ hV ↦
    isZero_rightDerived_sectionsFunctorAt_opensEtale _ F q (h _ hV)

end AlgebraicGeometry.Scheme
