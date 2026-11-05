import Langlands.AlgebraicGeometry.Modules.CohomologyBaseChange
import Langlands.AlgebraicGeometry.Modules.PushforwardVanishing
import Langlands.AlgebraicGeometry.Modules.ClosedImmersionHigherDirectImageVanishingProof

/-! # Relative cohomology of a map into a closed-immersion pushforward -/

noncomputable section

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

namespace Langlands.AlgebraicGeometry.Modules.DerivedSections

variable {Y Z : Scheme.{u}} {R S : CommRingCat.{u}}
  (φ : R ⟶ S) (g : Y ⟶ Spec R) (g' : Z ⟶ Spec S)
  (h : Z ⟶ Y) [IsClosedImmersion h]
  (w : h ≫ g = g' ≫ Spec.map φ)

/-- The cohomology map of an actual sheaf map into a closed-immersion pushforward,
with scalar restriction along the specified base-ring map. -/
def closedImmersionCohomologyMap {M : Y.Modules} {N : Z.Modules}
    (a : M ⟶ (Scheme.Modules.pushforward h).obj N) (n : ℕ) :
    (relativeCohomology g n).obj M ⟶
      (ModuleCat.restrictScalars φ.hom).obj ((relativeCohomology g' n).obj N) :=
  (relativeCohomology g n).map a ≫
    (pushforwardCohomologyIso h g N
      (fun q => closedImmersionHigherDirectImageVanishing Z Y h inferInstance N q) n).inv ≫
    (relativeCohomologyBaseRingIso φ (h ≫ g) g' w n).hom.app N

/-- Commutative squares of actual sheaf maps induce commutative cohomology squares. -/
@[reassoc]
lemma closedImmersionCohomologyMap_naturality
    {M M' : Y.Modules} {N N' : Z.Modules}
    (a : M ⟶ (Scheme.Modules.pushforward h).obj N)
    (a' : M' ⟶ (Scheme.Modules.pushforward h).obj N')
    (b : M ⟶ M') (c : N ⟶ N')
    (sq : b ≫ a' = a ≫ (Scheme.Modules.pushforward h).map c) (n : ℕ) :
    (relativeCohomology g n).map b ≫
        closedImmersionCohomologyMap φ g g' h w a' n =
      closedImmersionCohomologyMap φ g g' h w a n ≫
        (ModuleCat.restrictScalars φ.hom).map ((relativeCohomology g' n).map c) := by
  let v (T : Z.Modules) (q : ℕ) :=
    closedImmersionHigherDirectImageVanishing Z Y h inferInstance T q
  have hn := pushforwardComparison_naturality h g c (v N) (v N') n
  change (relativeCohomology (h ≫ g) n).map c ≫
      (pushforwardCohomologyIso h g N' (v N') n).hom =
    (pushforwardCohomologyIso h g N (v N) n).hom ≫
      (relativeCohomology g n).map ((Scheme.Modules.pushforward h).map c) at hn
  have hi : (relativeCohomology g n).map ((Scheme.Modules.pushforward h).map c) ≫
        (pushforwardCohomologyIso h g N' (v N') n).inv =
      (pushforwardCohomologyIso h g N (v N) n).inv ≫
        (relativeCohomology (h ≫ g) n).map c := by
    apply (cancel_mono (pushforwardCohomologyIso h g N' (v N') n).hom).1
    simp only [Category.assoc, Iso.inv_hom_id, Category.comp_id]
    rw [hn, Iso.inv_hom_id_assoc]
  have hb := (relativeCohomologyBaseRingIso φ (h ≫ g) g' w n).hom.naturality c
  simp only [Functor.comp_map] at hb
  simp only [closedImmersionCohomologyMap, Category.assoc]
  rw [← Functor.map_comp_assoc, sq, Functor.map_comp_assoc,
    reassoc_of% hi, hb]

end Langlands.AlgebraicGeometry.Modules.DerivedSections
