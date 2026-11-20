import Langlands.AbelianScheme.PolarizedFiniteLevel.ModuliZariskiSheafOfRigidityStatement
import Langlands.AbelianScheme.PolarizedFiniteLevel.EventualModuliZariskiSheafReduction
import Langlands.AbelianScheme.PolarizedFiniteLevel.ZariskiSeparation
import Langlands.AbelianScheme.PolarizedFiniteLevel.ZariskiLocality
import Langlands.AbelianScheme.PolarizedFiniteLevel.ZariskiGluingDatum

/-! # Rigidity of polarized automorphisms implies the Zariski sheaf property: proof -/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry Opposite

namespace Langlands.AbelianScheme.PolarizedFiniteLevel

namespace ZariskiGluing

variable {P : Prerequisites.{u}} {g d n : ℕ} {S : Scheme.{u}} [QuasiSeparatedSpace S]
  {J : Type*} {U : J → S.Opens}

/-- **Existence of glued data.** Rigid data on the members of an open cover of a
quasi-separated scheme whose restrictions to the pairwise overlaps are isomorphic glue to a
datum on the whole scheme. -/
theorem exists_glue (hU : iSup U = ⊤) (a : ∀ i, Datum P (U i).toScheme g d n)
    (h : ∀ i j, Isomorphic ((a i).pullback (S.homOfLE (inf_le_left : U i ⊓ U j ≤ U i)))
      ((a j).pullback (S.homOfLE (inf_le_right : U i ⊓ U j ≤ U j))))
    (hrig : ∀ (W : SubOpens U) (α : PolarizedIso (localDatum a W) (localDatum a W)),
      α = PolarizedIso.refl (localDatum a W)) :
    ∃ b : Datum P S g d n, ∀ i, Isomorphic (b.pullback (U i).ι) (a i) := by
  let c := localDatum a
  let θ := transition h
  let F : SubOpens U → S.Opens := fun W => W.1
  have hF : iSup F = ⊤ := isOpenCover_subOpens hU
  have hdim : (gluedAbelian hU c hrig θ).HasRelativeDimension g :=
    hasRelativeDimension_of_opens F hF (gluedAbelian hU c hrig θ)
      (fun W => (localTransport hU c hrig θ W).dimension)
  have hpol : (gluedDualWitness hU c hrig θ).IsPolarization P (gluedPolarization hU c hrig θ) :=
    DualWitness.isPolarization_of_opens F hF P (gluedDualWitness hU c hrig θ)
      (gluedPolarization hU c hrig θ) (fun W => by
        rw [pullbackMap_gluedPolarization]
        exact (localTransport hU c hrig θ W).polarized)
  have hdeg : HasDegreeSquare (gluedPolarization hU c hrig θ) d :=
    hasDegreeSquare_of_opens F hF (gluedPolarization hU c hrig θ) hpol.1 (fun W => by
      rw [baseChange_map_gluedPolarization]
      exact HasDegreeSquare.post_iso (localTransport hU c hrig θ W).polarized.1
        (localTransport hU c hrig θ W).degree
        ((gluedDualWitness hU c hrig θ).baseChangeIso P W.1.ι
          ((gluedDualWitness hU c hrig θ).pullback P W.1.ι)).symm)
  have hfull : IsFull (gluedSections hU c hrig θ) :=
    isFull_of_opens F hF (gluedSections hU c hrig θ) (fun W => by
      rw [pullbackTuple_gluedSections]
      exact (localTransport hU c hrig θ W).level.full)
  exact ⟨gluedDatum hU c hrig θ hdim hpol hdeg hfull, isomorphic_restrict_of_subOpens h _
    (isomorphic_gluedDatum_restrict hU c hrig θ hdim hpol hdeg hfull)⟩

end ZariskiGluing

variable {P : Prerequisites.{0}} {g d n : ℕ}

/-- The sheaf condition from separation and an existence statement for glued data. -/
theorem isZariskiSheaf_of_exists_glue (hd : 0 < d) (hn : 3 ≤ n)
    (hrig : ∀ (T : LevelBase n) (c : Datum P T.obj g d n) (α : PolarizedIso c c),
      α = PolarizedIso.refl c)
    (hex : ∀ (S : LevelBase n) {I : Type} (U : I → S.obj.Opens) (_ : iSup U = ⊤)
      (a : ∀ i, Datum P (U i).toScheme g d n),
      (∀ i j, Isomorphic ((a i).pullback (S.obj.homOfLE (inf_le_left : U i ⊓ U j ≤ U i)))
        ((a j).pullback (S.obj.homOfLE (inf_le_right : U i ⊓ U j ≤ U j)))) →
      ∃ b : Datum P S.obj g d n, ∀ i, Isomorphic (b.pullback (U i).ι) (a i)) :
    LevelBase.IsZariskiSheaf (moduliFunctor P g d n hd hn) := by
  intro S I U hU s hs
  let a : ∀ i, Datum P (U i).toScheme g d n := fun i => (s i).out
  have ha : ∀ i, (a i).classOf = s i := fun i => Quotient.out_eq (s i)
  have h : ∀ i j, Isomorphic ((a i).pullback (S.obj.homOfLE (inf_le_left : U i ⊓ U j ≤ U i)))
      ((a j).pullback (S.obj.homOfLE (inf_le_right : U i ⊓ U j ≤ U j))) := by
    intro i j
    have e := hs i j
    rw [← ha i, ← ha j] at e
    exact Quotient.exact (show ((a i).pullback (S.obj.homOfLE inf_le_left)).classOf =
      ((a j).pullback (S.obj.homOfLE inf_le_right)).classOf from e)
  obtain ⟨b, hb⟩ := hex S U hU a h
  have hres : ∀ i, (moduliFunctor P g d n hd hn).map (S.openι (U i)).op b.classOf = s i := by
    intro i
    rw [← ha i]
    exact Quotient.sound (hb i)
  refine ⟨b.classOf, hres, fun t ht => ?_⟩
  exact moduliFunctor_separated hrig hd hn U hU t b.classOf
    (fun i => (ht i).trans (hres i).symm)

/-- **Rigidity implies the Zariski sheaf property.** Proof of
`ModuliZariskiSheafOfRigidityStatement`. -/
theorem moduliZariskiSheafOfRigidity : ModuliZariskiSheafOfRigidityStatement := by
  intro P g d n hd hn hrig
  apply isZariskiSheaf_of_exists_glue hd hn hrig
  intro S I U hU a h
  exact ZariskiGluing.exists_glue hU a h (fun W α => hrig (S.ofOpen W.1) _ α)

set_option linter.defProp false in
/-- Proved definition: Lefschetz's embedding theorem over fields alone implies the target
`EventualModuliZariskiSheafStatement`. -/
def eventualModuliZariskiSheaf_of_cubicFieldEmbedding
    (hL : CubicFieldEmbeddingStatement.{0}) : EventualModuliZariskiSheafStatement :=
  eventualModuliZariskiSheaf_of_rigidity hL moduliZariskiSheafOfRigidity

end Langlands.AbelianScheme.PolarizedFiniteLevel
