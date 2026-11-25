/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.DiagonalCoefficients.Coefficient.DiagonalCoefficientDiagrams
import WeilConjectures.AlgebraicGeometry.DiagonalCoefficients.Scalar.DiagonalScalarCompatibilityTriangle
import WeilConjectures.AlgebraicGeometry.DiagonalCoefficients.Closure.DiagonalClosureScalarFrame
import all WeilConjectures.AlgebraicGeometry.ProEtale.Tate.ProEtaleTateTwistConstructionsSupplement
import WeilConjectures.CategoryTheory.SixFunctors.IntegrationTransport

/-! # Coherence and closure of fixed finite coefficient diagrams

Source: diagonal tower coefficient changes, paragraph (2).
(blueprint: lem-sfb-diagonal-finite-coefficient-closure).
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option Elab.async false
set_option genSizeOf false
set_option genInjectivity false
set_option synthInstance.maxSize 4096
universe u
open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory Opposite
open scoped CategoryTheory.MonObj
open scoped CategoryTheory.Obj CategoryTheory.Functor
namespace AlgebraicGeometry.ProEtale.DiagonalCoefficients

attribute [local irreducible] derivedScalars RestrictionSquare.mate

private def semilinearOfAct
    {Λ Λ' : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1}}
    [MonObj Λ] [IsCommMonObj Λ] [MonObj Λ'] [IsCommMonObj Λ']
    (a : Λ ⟶ Λ') [IsMonHom a] (X : Scheme.{u})
    (M : Modules Λ X) (N : Modules Λ' X) (m : M.X ⟶ N.X)
    (h : Mod.act M.X ≫ m = (coefficientMap a X ⊗ₘ m) ≫ Mod.act N.X) :
    Semilinear a M N m where
  hom := Mod.Hom.mk' m (by
    change Mod.act M.X ≫ m =
      condensedRingObj Λ X ◁ m ≫ coefficientMap a X ▷ N.X ≫ Mod.act N.X
    rw [h, MonoidalCategory.tensorHom_def', Category.assoc])
  underlying := rfl

private def rationalTransition_semilinear
    (l : ℕ) [Fact l.Prime] (X : Scheme.{u})
    {E F : PadicAlgCl.FiniteIntermediateField l} (h : E ≤ F) :
    Semilinear (Profinite.padicSubfieldRingObjMap l h)
      (spRationalTwist X l E) (spRationalTwist X l F) (spRationalTwistMap X l h) :=
  semilinearOfAct _ X _ _ _ (spRationalTwistMap_semilinear X l h)

private def closureLine_semilinear
    (l : ℕ) [Fact l.Prime] (X : Scheme.{u}) (E : PadicAlgCl.FiniteIntermediateField l) :
    Semilinear (Profinite.padicSubfieldRingObjToPadicAlgCl l E)
      (spRationalTwist X l E) (spQbarTwist X l) (closureLineMap l E X) := by
  apply semilinearOfAct
  have h := (spQbarTwistAction_existsUnique X l).exists.choose_spec
    E E E (le_refl E) (le_refl E)
  simp only [Profinite.padicSubfieldRingObjMap_id, coefficientMap_id,
    spRationalTwistMap_id, id_tensorHom_id, Category.id_comp] at h
  exact h.symm

private theorem extensionUnit_natural
    {C : Type*} [Category C] [MonoidalCategory C] [BraidedCategory C]
    [HasCoequalizers C]
    [∀ Z : C, PreservesColimitsOfSize.{0, 0} (tensorLeft Z)]
    [∀ Z : C, PreservesColimitsOfSize.{0, 0} (tensorRight Z)]
    {R S A B : C} [MonObj R] [MonObj S] [MonObj A] [MonObj B]
    [IsCommMonObj R] [IsCommMonObj S] [IsCommMonObj A] [IsCommMonObj B]
    (p : R ⟶ A) [IsMonHom p] (q : S ⟶ B) [IsMonHom q]
    (c : A ⟶ B) [IsMonHom c] (M : Mod C R) (N : Mod C S)
    (g : M.X ⟶ N.X)
    (f : (Mod.extendScalarsObj p M).X ⟶ (Mod.extendScalarsObj q N).X)
    (hf : Mod.extendπ p M ≫ f = (c ⊗ₘ g) ≫ Mod.extendπ q N) :
    Mod.extendUnitHom p M ≫ f = g ≫ Mod.extendUnitHom q N := by
  simp only [Mod.extendUnitHom, Category.assoc]
  rw [hf, MonoidalCategory.tensorHom_def]
  simp only [Category.assoc]
  rw [← comp_whiskerRight_assoc,
    IsMonHom.one_hom, ← whisker_exchange_assoc, leftUnitor_inv_naturality_assoc]

private theorem rationalCoefficient_triangle
    (l : ℕ) [Fact l.Prime] {E F : PadicAlgCl.FiniteIntermediateField l} (h : E ≤ F) :
    (integralMap.{u} l E ≫ padicIntegersRingObjToContinuousMapRingObj l E) ≫
        Profinite.padicSubfieldRingObjMap l h =
      integralMap l F ≫ padicIntegersRingObjToContinuousMapRingObj l F := by
  ext S x
  rfl

private theorem integralLine_triangle
    (l : ℕ) [Fact l.Prime] (X : Scheme.{u})
    {E F H : PadicAlgCl.FiniteIntermediateField l} (h : E ≤ F) (k : F ≤ H) :
    spIntegralTwistMap X l h ≫ spIntegralTwistMap X l k =
      spIntegralTwistMap X l (h.trans k) := by
  have hc : coefficientMap.{u} (Profinite.padicSubfieldRingObjMap l (h.trans k)) X =
      coefficientMap.{u} (Profinite.padicSubfieldRingObjMap l h) X ≫
        coefficientMap.{u} (Profinite.padicSubfieldRingObjMap l k) X := by
    rw [Profinite.padicSubfieldRingObjMap_comp, coefficientMap_comp]
  have hm : spIntegersMap X l (h.trans k) =
      spIntegersMap X l h ≫ spIntegersMap X l k := by
    have := (spIntegersMap_spec X l h).1
    have := (spIntegersMap_spec X l k).1
    apply (spIntegersMap_existsUnique X l (h.trans k)).unique
      (spIntegersMap_spec X l (h.trans k))
    refine ⟨inferInstance, ?_⟩
    calc
      _ = spIntegersMap X l h ≫ (spIntegersMap X l k ≫
          padicIntegersToPadicSubfield X l H) := Category.assoc _ _ _
      _ = _ := by
        rw [(spIntegersMap_spec X l k).2, ← Category.assoc, (spIntegersMap_spec X l h).2,
          Category.assoc, ← hc]
  have hn (n : ℕ) : spEllMap X l (h.trans k) n =
      spEllMap X l h n ≫ spEllMap X l k n := by
    apply (spEllMap_existsUnique X l (h.trans k) n).unique
      (spEllMap_spec X l (h.trans k) n)
    rw [← Category.assoc, spEllMap_spec X l h n, Category.assoc, spEllMap_spec X l k n,
      ← Category.assoc, ← hm]
  symm
  apply (spIntegralTwistMap_existsUnique X l (h.trans k)).unique
    (spIntegralTwistMap_spec X l (h.trans k))
  intro n
  rw [Category.assoc, spIntegralTwistMap_spec X l k n, ← Category.assoc,
    spIntegralTwistMap_spec X l h n, Category.assoc,
    MonoidalCategory.tensorHom_comp_tensorHom, Category.id_comp, ← hn n]

private theorem rationalLine_triangle
    (l : ℕ) [Fact l.Prime] (X : Scheme.{u})
    {E F : PadicAlgCl.FiniteIntermediateField l} (h : E ≤ F) :
    rationalLineMap l E X ≫ spRationalTwistMap X l h =
      spIntegralTwistMap X l h ≫ rationalLineMap l F X := by
  exact extensionUnit_natural (padicIntegersToPadicSubfield X l E)
    (padicIntegersToPadicSubfield X l F)
    (coefficientMap (Profinite.padicSubfieldRingObjMap l h) X)
    (spIntegralTwist X l E) (spIntegralTwist X l F)
    (spIntegralTwistMap X l h) (spRationalTwistMap X l h)
    (spRationalTwistMap_spec X l h)

private theorem bottomField_le
    (l : ℕ) [Fact l.Prime] (E : PadicAlgCl.FiniteIntermediateField l) :
    bottomField l ≤ E :=
  show (⊥ : IntermediateField ℚ_[l] (PadicAlgCl l)) ≤ E.1 from bot_le

private theorem zlRationalLine_triangle
    (l : ℕ) [Fact l.Prime] (X : Scheme.{u})
    {E F : PadicAlgCl.FiniteIntermediateField l} (h : E ≤ F) :
    (integralLineMap l E X ≫ rationalLineMap l E X) ≫ spRationalTwistMap X l h =
      integralLineMap l F X ≫ rationalLineMap l F X := by
  change (spIntegralTwistMap X l (E := bottomField l) (F := E) (bottomField_le l E) ≫
      rationalLineMap l E X) ≫ spRationalTwistMap X l h =
    spIntegralTwistMap X l (E := bottomField l) (F := F) (bottomField_le l F) ≫
      rationalLineMap l F X
  rw [Category.assoc, rationalLine_triangle l X h, ← Category.assoc,
    integralLine_triangle]

private theorem scalarFrame_diagram
    {Λ Λ' : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1}}
    [MonObj Λ] [IsCommMonObj Λ] [MonObj Λ'] [IsCommMonObj Λ']
    (a : Λ ⟶ Λ') [IsMonHom a] (Y : Scheme.{u})
    (L : ∀ X : Scheme.{u}, Modules Λ X) (L' : ∀ X : Scheme.{u}, Modules Λ' X)
    (m : ∀ X : Scheme.{u}, (L X).X ⟶ (L' X).X) (d₀ : Diagram Λ Y L)
    (e : ScalarFrame a Y L L' m d₀) :
    ∃ d : Diagram Λ' Y L', Nonempty (ScalarCompatibility a Y L L' m d₀ d) := by
  let Rq := scalarRightDerived Λ' (ProjectiveLine Y ↘ Y)
  let R₁ := scalarRightDerived Λ'
    (pullback.fst (ProjectiveLine Y ↘ Y) (ProjectiveLine Y ↘ Y))
  let R₂ := scalarRightDerived Λ'
    (pullback.snd (ProjectiveLine Y ↘ Y) (ProjectiveLine Y ↘ Y))
  let U := derivedScalars a (diagonalSurface Y)
  let V := derivedScalars a (ProjectiveLine Y)
  let := e.q_iso
  let := e.p₁_iso
  let := e.p₂_iso
  have hlineP : IsIso (e.lineP.shift a) := by
    dsimp only [Endpoint.shift]
    infer_instance
  have hlineW : IsIso (e.lineW.shift a) := by
    dsimp only [Endpoint.shift]
    infer_instance
  let := hlineP
  let := hlineW
  let delta := e.supported.iso.inv ≫ U.map d₀.delta ≫ e.lineW.shift a
  let traceq := inv ((e.q.mate a).app _ ≫ Rq.R.map (e.lineP.shift a)) ≫
    (derivedScalars a Y).map d₀.traceq ≫ (e.units Y).iso.hom
  let trace₁ := inv ((e.p₁.mate a).app _ ≫ R₁.R.map (e.lineW.shift a)) ≫
    V.map d₀.trace₁ ≫ (e.units (ProjectiveLine Y)).iso.hom
  let trace₂ := inv ((e.p₂.mate a).app _ ≫ R₂.R.map (e.lineW.shift a)) ≫
    V.map d₀.trace₂ ≫ (e.units (ProjectiveLine Y)).iso.hom
  have hdelta : U.map d₀.delta ≫ e.lineW.shift a =
      e.supported.iso.hom ≫ delta := by
    dsimp only [delta]
    simp only [Iso.hom_inv_id_assoc]
  have htraceq : (derivedScalars a Y).map d₀.traceq ≫ (e.units Y).iso.hom =
      (e.q.mate a).app _ ≫ Rq.R.map (e.lineP.shift a) ≫ traceq := by
    dsimp only [traceq]
    simp only [← Category.assoc, IsIso.hom_inv_id, Category.id_comp]
  have htrace₁ : V.map d₀.trace₁ ≫ (e.units (ProjectiveLine Y)).iso.hom =
      (e.p₁.mate a).app _ ≫ R₁.R.map (e.lineW.shift a) ≫ trace₁ := by
    dsimp only [trace₁]
    simp only [← Category.assoc, IsIso.hom_inv_id, Category.id_comp]
  have htrace₂ : V.map d₀.trace₂ ≫ (e.units (ProjectiveLine Y)).iso.hom =
      (e.p₂.mate a).app _ ≫ R₂.R.map (e.lineW.shift a) ≫ trace₂ := by
    dsimp only [trace₂]
    simp only [← Category.assoc, IsIso.hom_inv_id, Category.id_comp]
  let d : Diagram Λ' Y L' :=
    { Rq := Rq
      R₁ := R₁
      R₂ := R₂
      q_canonical := rfl
      p₁_canonical := rfl
      p₂_canonical := rfl
      q_unit := by intro K; exact Category.comp_id _
      p₁_unit := by intro K; exact Category.comp_id _
      p₂_unit := by intro K; exact Category.comp_id _
      delta := delta
      traceq := traceq
      trace₁ := trace₁
      trace₂ := trace₂
      support₁ := e.support₁
      support₂ := e.support₂
      integration₁ := integration_transport d₀.R₁.R R₁.R U V
        (e.p₁.mate a) e.supported.iso.hom (e.lineW.shift a)
        (e.units (ProjectiveLine Y)).iso d₀.support₁.hom d₀.delta d₀.trace₁
        e.support₁.hom delta trace₁ e.source₁ hdelta htrace₁ d₀.integration₁
      integration₂ := integration_transport d₀.R₂.R R₂.R U V
        (e.p₂.mate a) e.supported.iso.hom (e.lineW.shift a)
        (e.units (ProjectiveLine Y)).iso d₀.support₂.hom d₀.delta d₀.trace₂
        e.support₂.hom delta trace₂ e.source₂ hdelta htrace₂ d₀.integration₂ }
  let scalar : ScalarCompatibility a Y L L' m d₀ d :=
    { units := e.units
      lineP := e.lineP
      lineW := e.lineW
      supported := e.supported
      q := { square := e.q, comparison_iso := e.q_iso, trace := htraceq }
      p₁ := { square := e.p₁, comparison_iso := e.p₁_iso, trace := htrace₁ }
      p₂ := { square := e.p₂, comparison_iso := e.p₂_iso, trace := htrace₂ }
      delta := hdelta }
  exact ⟨d, ⟨scalar⟩⟩

/-- Fixed finite diagrams obtained from one Z_l diagram admit the prescribed
rational transitions and a common algebraic-closure diagram. The integral and
rational diagrams are input here; this theorem does not construct either.

Source: blueprint latest, sec-six-functors-basics/sk-prop-diagonal-tower/
sk-prop-diagonal-tower-coefficients.proof.md, paragraph (2), finite-field colimit
and compatibility of its legs.
(blueprint: lem-sfb-diagonal-finite-coefficient-closure).

Proof: Derive exact coefficient restriction with the normalized universal unit
and take its scalar mate. For E contained in F, associativity of extension of
scalars and the coefficient/root-map composition equations identify the
composite Z_l-to-O_E-to-E-to-F endpoint with the Z_l-to-O_F-to-F endpoint.
Adjunction injectivity gives the same equality for normalized direct-image
mates. Transport the two given scalar compatibility squares along these
identifications; since their source is the same fixed Z_l diagram, their
resulting diagonal and trace arrows agree. This constructs the required
rational transition compatibilities, including identity inclusions, with the
specified spRationalTwistMap maps. The poset of finite subextensions is
filtered. Its coefficient colimit is the prescribed condensed algebraic closure
and its root-line colimit is spQbarTwist. The regular objects and root lines
shifted by two have common lower bound -2. Since the three projections are
qcqs, bounded continuity identifies direct image of these colimits with the
colimits of direct images. Closed-diagonal direct image is exact and has the
same comparison on the supported coefficient source. Use these canonical
scalar endpoints and scalar/direct-image mates to transport a rational
diagram to the closure. Compatibility of all finite legs, just proved, makes
the result independent of the chosen initial finite subextension. Naturality
transports both integration identities. Normalize every endpoint by its adjoint
and every derived restriction square by its full universal unit. Associativity
and the colimit-leg equations then give ScalarCompatibility for every finite
rational diagram to this one closure diagram, with the prescribed closureLineMap.
The construction changes none of the input finite diagrams. -/
theorem diagonalCoefficient_finiteClosure
    (l : ℕ) [Fact l.Prime] (Y : Scheme.{u})
    [IsNoetherian Y] [IsNoetherian (ProjectiveLine Y)] [IsNoetherian (diagonalSurface Y)]
    (hY : IsUnit (l : Γ(Y, ⊤)))
    (d : Diagram (Profinite.continuousMapRingObj.{u} ℤ_[l]) Y (zlLine l))
    (i : ∀ E : PadicAlgCl.FiniteIntermediateField l,
      Diagram (Profinite.padicIntegersRingObj.{u} l E.1) Y
        (fun X ↦ spIntegralTwist X l E))
    (r : ∀ E : PadicAlgCl.FiniteIntermediateField l,
      Diagram (Profinite.continuousMapRingObj.{u} E.1) Y
        (fun X ↦ spRationalTwist X l E))
    (hi : ∀ E : PadicAlgCl.FiniteIntermediateField l,
      ScalarCompatibility (integralMap l E) Y (zlLine l)
        (fun X ↦ spIntegralTwist X l E) (integralLineMap l E) d (i E))
    (hr : ∀ E : PadicAlgCl.FiniteIntermediateField l,
      ScalarCompatibility (padicIntegersRingObjToContinuousMapRingObj l E) Y
        (fun X ↦ spIntegralTwist X l E) (fun X ↦ spRationalTwist X l E)
        (rationalLineMap l E) (i E) (r E)) :
    ∃ c : Diagram (Profinite.padicAlgClRingObj.{u} l) Y (fun X ↦ spQbarTwist X l),
      (∀ E : PadicAlgCl.FiniteIntermediateField l,
        Nonempty (ScalarCompatibility (Profinite.padicSubfieldRingObjToPadicAlgCl l E) Y
          (fun X ↦ spRationalTwist X l E) (fun X ↦ spQbarTwist X l)
          (closureLineMap l E) (r E) c)) ∧
      ∀ (E F : PadicAlgCl.FiniteIntermediateField l) (h : E ≤ F),
        Nonempty (ScalarCompatibility (Profinite.padicSubfieldRingObjMap l h) Y
          (fun X ↦ spRationalTwist X l E) (fun X ↦ spRationalTwist X l F)
          (fun X ↦ spRationalTwistMap X l (E := E) (F := F) h) (r E) (r F)) := by
  classical
  let a (E : PadicAlgCl.FiniteIntermediateField l) :=
    integralMap.{u} l E ≫ padicIntegersRingObjToContinuousMapRingObj l E
  let m (E : PadicAlgCl.FiniteIntermediateField l) (X : Scheme.{u}) :=
    integralLineMap l E X ≫ rationalLineMap l E X
  have base (E : PadicAlgCl.FiniteIntermediateField l) :
      Nonempty (ScalarCompatibility (a E) Y (zlLine l)
        (fun X ↦ spRationalTwist X l E) (m E) d (r E)) :=
    (scalarCompatibility_triangle (integralMap l E)
      (padicIntegersRingObjToContinuousMapRingObj l E) (a E) Y
      (zlLine l) (fun X ↦ spIntegralTwist X l E) (fun X ↦ spRationalTwist X l E)
      (integralLineMap l E) (rationalLineMap l E) (m E)
      d (i E) (r E) rfl (fun _ ↦ rfl) (hi E)
      (hr E).lineP.semilinear (hr E).lineW.semilinear).mpr ⟨hr E⟩
  have transitions (E F : PadicAlgCl.FiniteIntermediateField l) (h : E ≤ F) :
      Nonempty (ScalarCompatibility (Profinite.padicSubfieldRingObjMap l h) Y
        (fun X ↦ spRationalTwist X l E) (fun X ↦ spRationalTwist X l F)
        (fun X ↦ spRationalTwistMap X l h) (r E) (r F)) :=
    (scalarCompatibility_triangle (a E) (Profinite.padicSubfieldRingObjMap l h) (a F) Y
      (zlLine l) (fun X ↦ spRationalTwist X l E) (fun X ↦ spRationalTwist X l F)
      (m E) (fun X ↦ spRationalTwistMap X l h) (m F)
      d (r E) (r F) (rationalCoefficient_triangle l h)
      (fun X ↦ zlRationalLine_triangle l X h) (base E).some
      (rationalTransition_semilinear l (ProjectiveLine Y) h)
      (rationalTransition_semilinear l (diagonalSurface Y) h)).mp (base F)
  let E₀ := bottomField l
  obtain ⟨frame⟩ := diagonalClosure_scalarFrame l Y hY E₀ (r E₀)
  obtain ⟨c, hc⟩ := scalarFrame_diagram
    (Profinite.padicSubfieldRingObjToPadicAlgCl l E₀) Y
    (fun X ↦ spRationalTwist X l E₀) (fun X ↦ spQbarTwist X l)
    (closureLineMap l E₀) (r E₀) frame
  let aC := a E₀ ≫ Profinite.padicSubfieldRingObjToPadicAlgCl l E₀
  let mC (X : Scheme.{u}) := m E₀ X ≫ closureLineMap l E₀ X
  have closureBase : Nonempty (ScalarCompatibility aC Y (zlLine l)
      (fun X ↦ spQbarTwist X l) mC d c) :=
    (scalarCompatibility_triangle (a E₀)
      (Profinite.padicSubfieldRingObjToPadicAlgCl l E₀) aC Y
      (zlLine l) (fun X ↦ spRationalTwist X l E₀) (fun X ↦ spQbarTwist X l)
      (m E₀) (closureLineMap l E₀) mC d (r E₀) c
      rfl (fun _ ↦ rfl) (base E₀).some
      (closureLine_semilinear l (ProjectiveLine Y) E₀)
      (closureLine_semilinear l (diagonalSurface Y) E₀)).mpr hc
  refine ⟨c, ?_, transitions⟩
  intro E
  have h : E₀ ≤ E := bottomField_le l E
  have hcoeff : a E ≫ Profinite.padicSubfieldRingObjToPadicAlgCl l E = aC := by
    change a E ≫ Profinite.padicSubfieldRingObjToPadicAlgCl l E =
      a E₀ ≫ Profinite.padicSubfieldRingObjToPadicAlgCl l E₀
    dsimp only [a]
    rw [← rationalCoefficient_triangle l h, Category.assoc,
      Profinite.padicSubfieldRingObjMap_comp_toPadicAlgCl]
  have hline (X : Scheme.{u}) : m E X ≫ closureLineMap l E X = mC X := by
    change m E X ≫ closureLineMap l E X = m E₀ X ≫ closureLineMap l E₀ X
    dsimp only [m]
    rw [← zlRationalLine_triangle l X h, Category.assoc]
    congr 1
    exact colimit.w (spRationalTwistDiagram X l) (homOfLE h)
  exact (scalarCompatibility_triangle (a E)
    (Profinite.padicSubfieldRingObjToPadicAlgCl l E) aC Y
    (zlLine l) (fun X ↦ spRationalTwist X l E) (fun X ↦ spQbarTwist X l)
    (m E) (closureLineMap l E) mC d (r E) c hcoeff hline (base E).some
    (closureLine_semilinear l (ProjectiveLine Y) E)
    (closureLine_semilinear l (diagonalSurface Y) E)).mp closureBase

end AlgebraicGeometry.ProEtale.DiagonalCoefficients
