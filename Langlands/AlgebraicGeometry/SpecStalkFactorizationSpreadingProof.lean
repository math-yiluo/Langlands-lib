import Mathlib.AlgebraicGeometry.AffineTransitionLimit
import Mathlib.AlgebraicGeometry.Stalk
import Langlands.AlgebraicGeometry.SpecStalkFactorizationSpreadingStatement

/-! # Spreading out a factorization from the local scheme at a point -/

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry TopologicalSpace Opposite

set_option backward.isDefEq.respectTransparency false

namespace Langlands.AlgebraicGeometry

namespace SpecStalkFactorizationSpreading

variable {S : Scheme.{u}} (s : S)

/-- The affine open neighbourhoods of `s`, ordered by inclusion. -/
abbrev AffineNhds : Type u := {U : S.Opens // s ∈ U ∧ IsAffineOpen U}

instance : IsCodirectedOrder (AffineNhds s) := ⟨fun U V => by
  obtain ⟨W, hW, hsW, hWUV⟩ :=
    exists_isAffineOpen_mem_and_subset (x := s) (U := U.1 ⊓ V.1) ⟨U.2.1, V.2.1⟩
  exact ⟨⟨W, hsW, hW⟩, fun x hx => (hWUV hx).1, fun x hx => (hWUV hx).2⟩⟩

instance : Nonempty (AffineNhds s) := by
  obtain ⟨W, hW, hsW, -⟩ := exists_isAffineOpen_mem_and_subset (x := s) (U := ⊤) trivial
  exact ⟨⟨W, hsW, hW⟩⟩

/-- The underlying open neighbourhood of an affine open neighbourhood. -/
def toOpenNhds (U : AffineNhds s) : OpenNhds s := ⟨U.1, U.2.1⟩

lemma toOpenNhds_mono : Monotone (toOpenNhds s) := fun _ _ h => h

/-- The inclusion of the affine open neighbourhoods into all open neighbourhoods of `s`. -/
abbrev incl : AffineNhds s ⥤ OpenNhds s := (toOpenNhds_mono s).functor

instance : (incl s).Initial :=
  (Monotone.initial_functor_iff _).mpr fun U => by
    obtain ⟨W, hW, hsW, hWU⟩ := exists_isAffineOpen_mem_and_subset (x := s) U.2
    exact ⟨⟨W, hsW, hW⟩, hWU⟩

/-- The rings of sections `Γ(S, U)` over the affine open neighbourhoods `U` of `s`. -/
abbrev sectionsDiagram : (AffineNhds s)ᵒᵖ ⥤ CommRingCat.{u} :=
  (incl s).op ⋙ ((OpenNhds.inclusion s).op ⋙ S.presheaf)

/-- The cocone of germ maps `Γ(S, U) ⟶ 𝒪_{S,s}`. -/
noncomputable def germCocone : Cocone (sectionsDiagram s) :=
  (colimit.cocone ((OpenNhds.inclusion s).op ⋙ S.presheaf)).whisker (incl s).op

/-- The germ cocone is a colimit, since affine neighbourhoods are cofinal. -/
noncomputable def isColimitGermCocone : IsColimit (germCocone s) :=
  (Functor.Final.isColimitWhiskerEquiv (incl s).op _).symm (colimit.isColimit _)

/-- The diagram of affine schemes `Spec Γ(S, U)`. -/
noncomputable abbrev specDiagram : AffineNhds s ⥤ Scheme.{u} :=
  (sectionsDiagram s).rightOp ⋙ Scheme.Spec

instance (U : AffineNhds s) : IsAffine ((specDiagram s).obj U) :=
  inferInstanceAs (IsAffine (Spec (S.presheaf.obj (op U.1))))

/-- The cone `Spec 𝒪_{S,s} ⟶ Spec Γ(S, U)`. -/
noncomputable def specCone : Cone (specDiagram s) :=
  Scheme.Spec.mapCone (coneRightOpOfCocone (germCocone s))

/-- `Spec 𝒪_{S,s}` is the limit of the `Spec Γ(S, U)`. -/
noncomputable def isLimitSpecCone : IsLimit (specCone s) :=
  isLimitOfPreserves Scheme.Spec (isLimitConeRightOpOfCocone _ (isColimitGermCocone s))

/-- The canonical morphism `Spec Γ(S, U) ⟶ S`. -/
noncomputable def specToBase (U : AffineNhds s) : (specDiagram s).obj U ⟶ S := U.2.2.fromSpec

lemma specDiagram_map_specToBase {U V : AffineNhds s} (f : U ⟶ V) :
    (specDiagram s).map f ≫ specToBase s V = specToBase s U :=
  V.2.2.map_fromSpec U.2.2 _

lemma specCone_π_specToBase (U : AffineNhds s) :
    (specCone s).π.app U ≫ specToBase s U = S.fromSpecStalk s := by
  rw [← U.2.2.fromSpecStalk_eq_fromSpecStalk U.2.1]
  rfl

variable {X : Scheme.{u}} (p : X ⟶ S)

/-- The diagram `X ×_S Spec Γ(S, U)`. -/
noncomputable def pullbackDiagram : AffineNhds s ⥤ Scheme.{u} where
  obj U := pullback p (specToBase s U)
  map {U V} f := pullback.map p (specToBase s U) p (specToBase s V) (𝟙 X)
    ((specDiagram s).map f) (𝟙 S) (by simp) (by rw [Category.comp_id, specDiagram_map_specToBase])
  map_id U := by apply pullback.hom_ext <;> simp
  map_comp f g := by apply pullback.hom_ext <;> simp

/-- The projections `X ×_S Spec Γ(S, U) ⟶ Spec Γ(S, U)`. -/
noncomputable def pullbackToSpec : pullbackDiagram s p ⟶ specDiagram s where
  app U := pullback.snd p (specToBase s U)
  naturality U V f := by simp [pullbackDiagram]

/-- The projections `X ×_S Spec Γ(S, U) ⟶ X`. -/
noncomputable def pullbackToX : pullbackDiagram s p ⟶ (Functor.const (AffineNhds s)).obj X where
  app U := pullback.fst p (specToBase s U)
  naturality U V f := by simp [pullbackDiagram]

/-- The cone `X ×_S Spec 𝒪_{S,s} ⟶ X ×_S Spec Γ(S, U)`. -/
noncomputable def pullbackCone : Cone (pullbackDiagram s p) where
  pt := pullback p (S.fromSpecStalk s)
  π :=
    { app U := pullback.map p (S.fromSpecStalk s) p (specToBase s U) (𝟙 X)
        ((specCone s).π.app U) (𝟙 S) (by simp) (by rw [Category.comp_id, specCone_π_specToBase])
      naturality U V f := by
        apply pullback.hom_ext
        · simp [pullbackDiagram]
        · simp [pullbackDiagram]
          exact congrArg (pullback.snd p (S.fromSpecStalk s) ≫ ·) ((specCone s).w f).symm }

lemma pullbackCone_π_fst (U : AffineNhds s) :
    (pullbackCone s p).π.app U ≫ pullback.fst p (specToBase s U) =
      pullback.fst p (S.fromSpecStalk s) := by
  simp [pullbackCone]

lemma pullbackCone_π_snd (U : AffineNhds s) :
    (pullbackCone s p).π.app U ≫ pullback.snd p (specToBase s U) =
      pullback.snd p (S.fromSpecStalk s) ≫ (specCone s).π.app U := by
  simp [pullbackCone]

lemma isPullback_pullbackCone (U : AffineNhds s) :
    IsPullback ((pullbackCone s p).π.app U) (pullback.snd p (S.fromSpecStalk s))
      (pullback.snd p (specToBase s U)) ((specCone s).π.app U) := by
  refine IsPullback.of_right (h₁₂ := pullback.fst p (specToBase s U))
    (h₂₂ := specToBase s U) (v₁₃ := p) ?_ (pullbackCone_π_snd s p U)
    (IsPullback.of_hasPullback _ _)
  rw [pullbackCone_π_fst, specCone_π_specToBase]
  exact IsPullback.of_hasPullback p (S.fromSpecStalk s)

/-- `X ×_S Spec 𝒪_{S,s}` is the limit of the `X ×_S Spec Γ(S, U)`. -/
noncomputable def isLimitPullbackCone : IsLimit (pullbackCone s p) :=
  haveI := IsCofiltered.isConnected (AffineNhds s)
  isLimitOfIsPullbackOfIsConnected (pullbackToSpec s p) (pullbackCone s p) (specCone s)
    { hom := pullback.snd p (S.fromSpecStalk s)
      w U := (pullbackCone_π_snd s p U).symm }
    (isPullback_pullbackCone s p) (isLimitSpecCone s)

lemma pullbackDiagram_map_fst {U V : AffineNhds s} (f : U ⟶ V) :
    (pullbackDiagram s p).map f ≫ pullback.fst p (specToBase s V) =
      pullback.fst p (specToBase s U) := by
  simp [pullbackDiagram]

lemma pullbackDiagram_map_snd {U V : AffineNhds s} (f : U ⟶ V) :
    (pullbackDiagram s p).map f ≫ pullback.snd p (specToBase s V) =
      pullback.snd p (specToBase s U) ≫ (specDiagram s).map f := by
  simp [pullbackDiagram]

lemma isPullback_pullbackDiagram_map {U V : AffineNhds s} (f : U ⟶ V) :
    IsPullback (pullback.snd p (specToBase s U)) ((pullbackDiagram s p).map f)
      ((specDiagram s).map f) (pullback.snd p (specToBase s V)) := by
  refine IsPullback.flip (IsPullback.of_right (h₁₂ := pullback.fst p (specToBase s V))
    (h₂₂ := specToBase s V) (v₁₃ := p) ?_ (pullbackDiagram_map_snd s p f)
    (IsPullback.of_hasPullback _ _))
  rw [pullbackDiagram_map_fst, specDiagram_map_specToBase]
  exact IsPullback.of_hasPullback p (specToBase s U)

instance {U V : AffineNhds s} (f : U ⟶ V) : IsAffineHom ((pullbackDiagram s p).map f) :=
  MorphismProperty.of_isPullback (P := @IsAffineHom) (isPullback_pullbackDiagram_map s p f)
    inferInstance

end SpecStalkFactorizationSpreading

open SpecStalkFactorizationSpreading in
/-- **Spreading out a factorization from `Spec 𝒪_{S,s}`** (EGA IV₃, 8.8.2 (i)). -/
theorem specStalkFactorizationSpreading : SpecStalkFactorizationSpreadingStatement.{u} := by
  intro S X K p k s hpc hps hk ⟨y, hy⟩
  have hcpt (U : AffineNhds s) : CompactSpace ((pullbackDiagram s p).obj U) :=
    QuasiCompact.compactSpace_of_compactSpace (pullback.snd p (specToBase s U))
  have hqs (U : AffineNhds s) : QuasiSeparatedSpace ((pullbackDiagram s p).obj U) :=
    quasiSeparatedSpace_of_quasiSeparated (pullback.snd p (specToBase s U))
  obtain ⟨U, g, -, hg⟩ := Scheme.exists_π_app_comp_eq_of_locallyOfFinitePresentation
    (pullbackDiagram s p) (pullbackToX s p) k (pullbackCone s p) (isLimitPullbackCone s p) y
    (by ext U; simp [pullbackToX, pullbackCone_π_fst]; exact hy.symm)
  refine ⟨U.1, U.2.1, pullback.lift (pullback.fst p U.1.ι)
    (pullback.snd p U.1.ι ≫ U.2.2.isoSpec.hom) ?_ ≫ g, ?_⟩
  · rw [Category.assoc,
      show U.2.2.isoSpec.hom ≫ specToBase s U = U.1.ι from U.2.2.isoSpec_hom_fromSpec]
    exact pullback.condition
  · rw [Category.assoc, hg]
    exact pullback.lift_fst _ _ _

end Langlands.AlgebraicGeometry
