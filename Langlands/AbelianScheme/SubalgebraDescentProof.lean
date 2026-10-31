/-
The lemmas `fg_restrictScalars`, `isNoetherianRing_of_fg` and `specMap_comp` and the order of
the descent stages are adapted from the namespace `NoethModel17` (lemmas `fg_restrictScalars`,
`isNoetherianRing_of_fg`, `specMap_val_comp` and the stages `stage0` to `stage_gc`) in
`P2M/Sol/S_AlgebraicGeometry_exists_fg_subalgebra_isPullback_smooth_isProper_geometricallyConnected.lean`
of the Anthropic Lean formalization of Fermat's Last Theorem
(commit 6e837e75355538c7f80bab5b956861e86c4eacc2), Copyright 2026 Anthropic, PBC, licensed under
the Apache License, Version 2.0; see `licenses/Anthropic-FLT/LICENSE`, `NOTICE` and
`ATTRIBUTION.md`. The adaptation works with the Library's group schemes `Grp (Over S)` and
abelian schemes instead of FLT's relative group laws, starts from the prime subring instead of
`ULift ℤ`, and changes the universe handling and the proofs accordingly.
-/
import Langlands.AbelianScheme.SubalgebraDescentReductionStatement
import Langlands.AbelianScheme.Tate.BaseChangeCoherence
import Langlands.AlgebraicGeometry.NoetherianApproximation.SchemeSubalgebraDescentProof
import Langlands.AbelianScheme.GroupSchemeSubalgebraDescentProof
import Langlands.AlgebraicGeometry.NoetherianApproximation.IsSeparatedSubalgebraDescentProof
import Langlands.AlgebraicGeometry.NoetherianApproximation.IsProperSubalgebraDescentProof
import Langlands.AlgebraicGeometry.NoetherianApproximation.SmoothSubalgebraDescentProof
import Langlands.AlgebraicGeometry.NoetherianApproximation.GeometricallyConnectedSubalgebraDescentProof

/-! # Descent of abelian schemes to finitely generated subrings -/

noncomputable section

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open Langlands.AlgebraicGeometry.NoetherianApproximation

namespace Langlands.AbelianScheme.SubalgebraDescentProof

variable {R : CommRingCat.{u}}

/-- A tower of finitely generated subalgebras is finitely generated over `ℤ`. -/
theorem fg_restrictScalars (R₁ : Subalgebra ℤ R) (T : Subalgebra ↥R₁ R)
    (h₁ : R₁.FG) (h₂ : T.FG) : (T.restrictScalars ℤ).FG := by
  have i1 : Algebra.FiniteType ℤ ↥R₁ := (Subalgebra.fg_iff_finiteType _).1 h₁
  have i2 : Algebra.FiniteType ↥R₁ ↥T := (Subalgebra.fg_iff_finiteType _).1 h₂
  have i3 : Algebra.FiniteType ℤ ↥T := Algebra.FiniteType.trans i1 i2
  exact (Subalgebra.fg_iff_finiteType (T.restrictScalars ℤ)).2 i3

/-- A finitely generated subring is noetherian. -/
theorem isNoetherianRing_of_fg (R₁ : Subalgebra ℤ R) (h : R₁.FG) : IsNoetherianRing ↥R₁ := by
  have : Algebra.FiniteType ℤ ↥R₁ := (Subalgebra.fg_iff_finiteType _).1 h
  exact Algebra.FiniteType.isNoetherianRing ℤ ↥R₁

/-- A morphism property stable under base change transfers along an isomorphism of group
schemes. -/
theorem prop_of_iso (P : MorphismProperty Scheme.{u}) [P.IsStableUnderBaseChange]
    {S : Scheme.{u}} {G H : GroupScheme S} (e : G ≅ H) (h : P G.X.hom) : P H.X.hom := by
  let eL : G.X.left ≅ H.X.left := (Over.forget S).mapIso ((Grp.forget (Over S)).mapIso e)
  have sq : IsPullback eL.inv H.X.hom G.X.hom (𝟙 S) :=
    IsPullback.of_horiz_isIso ⟨by rw [Category.comp_id]; exact Over.w e.inv.hom.hom⟩
  exact MorphismProperty.of_isPullback sq h

/-- A morphism property stable under base change holds for the second projection. -/
theorem prop_snd (P : MorphismProperty Scheme.{u}) [P.IsStableUnderBaseChange]
    {X Y S : Scheme.{u}} (f : X ⟶ S) (g : Y ⟶ S) (h : P f) : P (pullback.snd f g) :=
  MorphismProperty.of_isPullback (IsPullback.of_hasPullback f g) h

/-- The composite of the two base-change maps of a tower of subalgebras. -/
theorem specMap_comp (R₁ : Subalgebra ℤ R) (T : Subalgebra ↥R₁ R) :
    Spec.map (CommRingCat.ofHom (algebraMap ↥R₁ R)) =
      Spec.map (CommRingCat.ofHom (algebraMap ↥T R)) ≫
        Spec.map (CommRingCat.ofHom (algebraMap ↥R₁ ↥T)) := by
  rw [← Spec.map_comp, ← CommRingCat.ofHom_comp]
  rfl

/-- A stage of the descent: a finitely generated subring `R₀` of `R` and a commutative group
scheme over `Spec R₀` whose base change is isomorphic to `A`. -/
structure Stage (A : AbelianScheme (Spec R)) where
  R₀ : Subalgebra ℤ R
  fg : R₀.FG
  G : GroupScheme (Spec (CommRingCat.of ↥R₀))
  comm : IsCommMonObj G.X
  e : A.toGrp ≅
    (GroupScheme.baseChange (Spec.map (CommRingCat.ofHom (algebraMap ↥R₀ R)))).obj G

/-- Base change of a stage to a finitely generated subalgebra over its ring. -/
def Stage.step {A : AbelianScheme (Spec R)} (M : Stage A) (T : Subalgebra ↥M.R₀ R)
    (hT : T.FG) : Stage A where
  R₀ := T.restrictScalars ℤ
  fg := fg_restrictScalars M.R₀ T M.fg hT
  G := (GroupScheme.baseChange (Spec.map (CommRingCat.ofHom (algebraMap ↥M.R₀ ↥T)))).obj M.G
  comm := by
    have := M.comm
    exact Functor.isCommMonObj_obj (F := Over.pullback _) (M := M.G.X)
  e := M.e ≪≫ eqToIso (by rw [specMap_comp M.R₀ T]; rfl) ≪≫
    GroupScheme.baseChangeCompIso _ _ M.G

/-- The underlying morphism of the stepped group scheme is the base change. -/
theorem Stage.step_hom {A : AbelianScheme (Spec R)} (M : Stage A) (T : Subalgebra ↥M.R₀ R)
    (hT : T.FG) :
    (M.step T hT).G.X.hom =
      pullback.snd M.G.X.hom (Spec.map (CommRingCat.ofHom (algebraMap ↥M.R₀ ↥T))) := rfl

/-- A property of the structure morphism of `A` holds for the base change of the stage to
`Spec R`. -/
theorem Stage.prop_baseChange {A : AbelianScheme (Spec R)} (M : Stage A)
    (P : MorphismProperty Scheme.{u}) [P.IsStableUnderBaseChange] (h : P A.X.hom) :
    P (pullback.snd M.G.X.hom (Spec.map (CommRingCat.ofHom (algebraMap ↥M.R₀ R)))) :=
  prop_of_iso P M.e h

/-- Finite generation over `ℤ` of a tower of finitely generated subalgebras over the prime
subring. -/
theorem fg_restrictScalars_bot (T₀ : Subalgebra ↥(⊥ : Subalgebra ℤ R) R)
    (T₁ : Subalgebra ↥T₀ R) (h₀ : T₀.FG) (h₁ : T₁.FG) : (T₁.restrictScalars ℤ).FG := by
  have i0 : Algebra.FiniteType ℤ ↥(⊥ : Subalgebra ℤ R) :=
    (Subalgebra.fg_iff_finiteType _).1 Subalgebra.fg_bot
  have i1 : Algebra.FiniteType ↥(⊥ : Subalgebra ℤ R) ↥T₀ := (Subalgebra.fg_iff_finiteType _).1 h₀
  have i2 : Algebra.FiniteType ↥T₀ ↥T₁ := (Subalgebra.fg_iff_finiteType _).1 h₁
  have i3 : Algebra.FiniteType ℤ ↥T₁ := Algebra.FiniteType.trans (Algebra.FiniteType.trans i0 i1) i2
  exact (Subalgebra.fg_iff_finiteType (T₁.restrictScalars ℤ)).2 i3

/-- The first stage: descend the scheme over the prime subring, then its group law. -/
theorem exists_stage₀ (hZM : SchemeSubalgebraDescentStatement.{u})
    (hGRP : GroupScheme.SubalgebraDescentStatement.{u}) (A : AbelianScheme (Spec R)) :
    ∃ M : Stage A, QuasiCompact M.G.X.hom ∧ QuasiSeparated M.G.X.hom ∧
      LocallyOfFinitePresentation M.G.X.hom := by
  unfold SchemeSubalgebraDescentStatement at hZM
  unfold GroupScheme.SubalgebraDescentStatement at hGRP
  obtain ⟨T₀, hT₀, -, X₀, f₀, π, hlfp, hqc, hqs, hπ⟩ :=
    hZM (A₀ := ↥(⊥ : Subalgebra ℤ R)) (A := R) A.X.hom (∅ : Finset R)
  have := hlfp
  have := hqc
  have := hqs
  obtain ⟨T₁, hT₁, -, G₀, a₀, ha₀, hcomm, ⟨e⟩⟩ :=
    hGRP (A₀ := ↥T₀) (A := R) f₀ A.toGrp π hπ (∅ : Finset R)
  refine ⟨{ R₀ := T₁.restrictScalars ℤ
            fg := fg_restrictScalars_bot T₀ T₁ hT₀ hT₁
            G := G₀
            comm := hcomm inferInstance
            e := e }, ?_, ?_, ?_⟩
  · exact MorphismProperty.of_isPullback (P := @QuasiCompact) ha₀ hqc
  · exact MorphismProperty.of_isPullback (P := @QuasiSeparated) ha₀ hqs
  · exact MorphismProperty.of_isPullback (P := @LocallyOfFinitePresentation) ha₀ hlfp

/-- Assembly: the abelian-scheme descent follows from the descent of schemes, group laws,
separatedness, properness, smoothness and geometric connectedness. -/
theorem subalgebraDescent_of (hZM : SchemeSubalgebraDescentStatement.{u})
    (hGRP : GroupScheme.SubalgebraDescentStatement.{u})
    (hSEP : IsSeparatedSubalgebraDescentStatement.{u})
    (hPR : IsProperSubalgebraDescentStatement.{u})
    (hSM : SmoothSubalgebraDescentStatement.{u})
    (hGC : GeometricallyConnectedSubalgebraDescentStatement.{u}) :
    AbelianScheme.SubalgebraDescentStatement.{u} := by
  unfold IsSeparatedSubalgebraDescentStatement at hSEP
  unfold IsProperSubalgebraDescentStatement at hPR
  unfold SmoothSubalgebraDescentStatement at hSM
  unfold GeometricallyConnectedSubalgebraDescentStatement at hGC
  intro R A
  obtain ⟨M₀, hqc₀, hqs₀, hlfp₀⟩ := exists_stage₀ hZM hGRP A
  -- separatedness
  have := hqc₀
  have := hqs₀
  have := M₀.prop_baseChange @IsSeparated (inferInstance : IsSeparated A.X.hom)
  obtain ⟨T₁, hT₁, -, hsep₁⟩ := hSEP (A₀ := ↥M₀.R₀) (A := R) M₀.G.X.hom (∅ : Finset R)
  let M₁ := M₀.step T₁ hT₁
  have hsep₁' : IsSeparated M₁.G.X.hom := hsep₁
  have hqc₁ : QuasiCompact M₁.G.X.hom := prop_snd @QuasiCompact _ _ hqc₀
  have hlfp₁ : LocallyOfFinitePresentation M₁.G.X.hom :=
    prop_snd @LocallyOfFinitePresentation _ _ hlfp₀
  -- properness
  have := isNoetherianRing_of_fg M₁.R₀ M₁.fg
  have := hsep₁'
  have := hqc₁
  have := hlfp₁
  have := M₁.prop_baseChange @IsProper (inferInstance : IsProper A.X.hom)
  obtain ⟨T₂, hT₂, -, hpr₂⟩ := hPR (A₀ := ↥M₁.R₀) (A := R) M₁.G.X.hom (∅ : Finset R)
  let M₂ := M₁.step T₂ hT₂
  have hpr₂' : IsProper M₂.G.X.hom := hpr₂
  have hlfp₂ : LocallyOfFinitePresentation M₂.G.X.hom :=
    prop_snd @LocallyOfFinitePresentation _ _ hlfp₁
  -- smoothness
  have := hpr₂'
  have := hlfp₂
  have := M₂.prop_baseChange @Smooth (inferInstance : Smooth A.X.hom)
  obtain ⟨T₃, hT₃, -, hsm₃⟩ := hSM (A₀ := ↥M₂.R₀) (A := R) M₂.G.X.hom (∅ : Finset R)
  let M₃ := M₂.step T₃ hT₃
  have hsm₃' : Smooth M₃.G.X.hom := hsm₃
  have hpr₃ : IsProper M₃.G.X.hom := prop_snd @IsProper _ _ hpr₂'
  -- geometric connectedness
  have := isNoetherianRing_of_fg M₃.R₀ M₃.fg
  have := hsm₃'
  have := hpr₃
  have := M₃.prop_baseChange @GeometricallyConnected
    (inferInstance : GeometricallyConnected A.X.hom)
  obtain ⟨T₄, hT₄, -, hgc₄⟩ := hGC (A₀ := ↥M₃.R₀) (A := R) M₃.G.X.hom (∅ : Finset R)
  let M₄ := M₃.step T₄ hT₄
  have hgc₄' : GeometricallyConnected M₄.G.X.hom := hgc₄
  have hsm₄ : Smooth M₄.G.X.hom := prop_snd @Smooth _ _ hsm₃'
  have hpr₄ : IsProper M₄.G.X.hom := prop_snd @IsProper _ _ hpr₃
  let A₀ : AbelianScheme (Spec (CommRingCat.of ↥M₄.R₀)) :=
    { toGrp := M₄.G
      comm := M₄.comm
      smooth := hsm₄
      proper := hpr₄
      geometricallyConnected := hgc₄' }
  exact ⟨M₄.R₀, M₄.fg, A₀,
    ⟨{ hom := Additive.ofMul M₄.e.hom
       inv := Additive.ofMul M₄.e.inv
       hom_inv_id := congrArg Additive.ofMul M₄.e.hom_inv_id
       inv_hom_id := congrArg Additive.ofMul M₄.e.inv_hom_id }⟩⟩

end Langlands.AbelianScheme.SubalgebraDescentProof

namespace Langlands.AbelianScheme

/-- Abelian schemes descend to finitely generated subrings, given the descent of schemes, group
laws and the four morphism properties. -/
theorem subalgebraDescentReduction : SubalgebraDescentReductionStatement.{u} :=
  fun hZM hGRP hSEP hPR hSM hGC =>
    SubalgebraDescentProof.subalgebraDescent_of hZM hGRP hSEP hPR hSM hGC

/-- Every abelian scheme over `Spec R` is isomorphic to the base change of an abelian scheme over
`Spec R₀`, for a finitely generated subring `R₀` of `R`. -/
theorem subalgebraDescent : Langlands.AbelianScheme.SubalgebraDescentStatement.{u} :=
  subalgebraDescentReduction schemeSubalgebraDescent GroupScheme.subalgebraDescent
    isSeparatedSubalgebraDescent isProperSubalgebraDescent smoothSubalgebraDescent
    geometricallyConnectedSubalgebraDescent

end Langlands.AbelianScheme
