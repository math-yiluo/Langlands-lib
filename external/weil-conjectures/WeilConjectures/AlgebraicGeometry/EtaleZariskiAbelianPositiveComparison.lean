/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.AlgebraicGeometry.EtaleTensorSectionsSheaf
public import Mathlib.CategoryTheory.Sites.SheafCohomology.Basic
public import WeilConjectures.AlgebraicGeometry.DerivedHomMayerVietoris
public import Mathlib.AlgebraicGeometry.Sites.AffineEtale
public import WeilConjectures.Mathlib.CategoryTheory.Abelian.GrothendieckAxioms.Sheaf
public import Mathlib.CategoryTheory.Abelian.GrothendieckCategory.EnoughInjectives
public import Mathlib.Algebra.Category.Grp.AB
import WeilConjectures.AlgebraicGeometry.ZariskiEtaleCore
import WeilConjectures.AlgebraicGeometry.EtaleTensorDirectImageIdentification
import WeilConjectures.AlgebraicGeometry.EtaleTensorPositiveDirectImageVanishing
import WeilConjectures.AlgebraicGeometry.EtaleZariskiNaturalAcyclicLeray

/-! # Positive-degree comparison for underlying abelian sheaves

Source: Stacks Project, Descent, Proposition Tag 03DW (2), and Étale Cohomology,
Theorem Tag 03P2 (blueprint: lem-sc-etale-zariski-abelian-positive-comparison).
-/

@[expose] public section

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Opposite TopologicalSpace

namespace AlgebraicGeometry.Scheme.Modules

set_option autoImplicit false

attribute [local irreducible] tensorPullback tensorPullbackObj

/-- In positive degrees, the underlying Zariski abelian sheaf of a quasi-coherent
module has the same cohomology as its associated tensor-sections étale sheaf.
The specified sheaf maps are the actual tensor pullbacks on every object.
This statement concerns abelian sheaf cohomology, not derived sections in the
category of modules, and makes no assertion in degree zero.

Source: Stacks Project, Descent, Proposition Tag 03DW (2), Étale Cohomology,
Theorem Tag 03P2, and Cohomology on Sites, Tags 03F3, 072W and 0733(1).
(blueprint: lem-sc-etale-zariski-abelian-positive-comparison).

Proof:
1. Include the open subschemes into the small étale site. On each open W,
   the unit-normalized identification of tensor pullback along its open immersion
   with module restriction identifies direct image of the tensor-sections sheaf
   with the underlying abelian sheaf of F. The unit equation of the pullback
   composition comparison makes these identifications commute with inclusions
   of opens. Naturality of the same adjunction comparison in F identifies the
   direct image of m F G φ with the underlying abelian sheaf map of φ.
2. On each affine open W, localization of sheaf cohomology identifies object
   cohomology of the tensor-sections sheaf with global étale cohomology of the
   sheaf associated to F restricted to W. Tensor pullback preserves
   quasi-coherence, so affine quasi-coherent acyclicity makes this group zero
   in every positive degree. Every open has an affine covering. Consequently
   every positive cohomology-presheaf section is locally zero, and its
   sheafification is zero. The sheafified-presheaf description of higher
   direct images gives vanishing of all positive derived direct images.
3. Apply Leray degeneration to this direct image. The edge map is the canonical
   cohomology pullback followed by the adjunction counit and is an isomorphism.
   Precompose it with cohomology of the direct-image identification in step 1.
   This yields the asserted additive equivalence for each positive degree.
4. The maps in step 3 are natural: use the square of step 1, functoriality of
   cohomology pullback, and naturality of the counit. Their composite is the
   displayed equality. The resolution interpretation of Ext identifies the
   small enough-injectives Zariski Ext model and the standard large étale Ext
   model with these same resolution maps, naturally in the coefficient sheaf.
   No separatedness, nonemptiness or smallness assumption on X is used. -/
theorem etaleZariskiAbelianPositiveComparison (X : Scheme.{u})
    (m : ∀ (F G : X.Modules) [F.IsQuasicoherent] [G.IsQuasicoherent],
      (F ⟶ G) → (etaleTensorSectionsSheaf F ⟶ etaleTensorSectionsSheaf G))
    (hm : ∀ (F G : X.Modules) [F.IsQuasicoherent] [G.IsQuasicoherent]
      (φ : F ⟶ G) (U : X.Etale),
      (m F G φ).hom.app (op U) = ((tensorPullback U.hom).map φ).app ⊤) :
    letI : EnoughInjectives
        (Sheaf (Opens.grothendieckTopology X.carrier) AddCommGrpCat.{u}) :=
      @IsGrothendieckAbelian.enoughInjectives _ _ _
        (Sheaf.isGrothendieckAbelian_of_essentiallySmall'.{u}
          (Opens.grothendieckTopology X.carrier) AddCommGrpCat.{u})
    letI : HasExt.{u}
        (Sheaf (Opens.grothendieckTopology X.carrier) AddCommGrpCat.{u}) :=
      hasExt_of_enoughInjectives _
    ∃ e : ∀ (F : X.Modules) [F.IsQuasicoherent] (n : ℕ),
        (Sheaf.H' ((SheafOfModules.toSheaf (moduleRings X.toRingedSpace)).obj F)
          (n + 1) (⊤ : X.Opens)) ≃+
        @Sheaf.H _ _ X.smallEtaleTopology (etaleTensorSectionsSheaf F)
          inferInstance (HasExt.standard _) (n + 1),
      ∀ (F G : X.Modules) [F.IsQuasicoherent] [G.IsQuasicoherent]
        (φ : F ⟶ G) (n : ℕ)
        (x : Sheaf.H'
          ((SheafOfModules.toSheaf (moduleRings X.toRingedSpace)).obj F)
          (n + 1) (⊤ : X.Opens)),
        e G n (((Sheaf.cohomologyPresheafFunctor
          (Opens.grothendieckTopology X.carrier) (n + 1)).map
            ((SheafOfModules.toSheaf (moduleRings X.toRingedSpace)).map φ)).app (op ⊤) x) =
        @Sheaf.H.map _ _ X.smallEtaleTopology inferInstance (HasExt.standard _)
          _ _ (m F G φ) (n + 1) (e F n x) := by
  classical
  let : EnoughInjectives
      (Sheaf (Opens.grothendieckTopology X.carrier) AddCommGrpCat.{u}) :=
    @IsGrothendieckAbelian.enoughInjectives _ _ _
      (Sheaf.isGrothendieckAbelian_of_essentiallySmall'.{u}
        (Opens.grothendieckTopology X.carrier) AddCommGrpCat.{u})
  let : HasExt.{u}
      (Sheaf (Opens.grothendieckTopology X.carrier) AddCommGrpCat.{u}) :=
    hasExt_of_enoughInjectives _
  obtain ⟨i, hi, _, hlim, ⟨hterminal⟩, hcont, _⟩ := zariski_to_etale_core X
  let := hcont
  let := hlim
  let T := i.sheafPushforwardContinuous AddCommGrpCat.{u}
    (Opens.grothendieckTopology X.carrier) X.smallEtaleTopology
  let : T.Additive := Functor.Additive.mk (by intros; rfl)
  obtain ⟨a, ha⟩ := etaleTensorDirectImageIdentification X i hi m hm
  have hacyc (F : X.Modules) [F.IsQuasicoherent] (n : ℕ) :
      IsZero ((T.rightDerived (n + 1)).obj (etaleTensorSectionsSheaf F)) :=
    etaleTensorPositiveDirectImageVanishing X i hi F n
  obtain ⟨b, hb⟩ := etaleZariskiNaturalAcyclicLeray X i hterminal
  let Q (n : ℕ) := Sheaf.cohomologyPresheafFunctor
    (Opens.grothendieckTopology X.carrier) (n + 1) ⋙
      (CategoryTheory.evaluation X.Opensᵒᵖ AddCommGrpCat.{u}).obj (op ⊤)
  let c (F : X.Modules) [F.IsQuasicoherent] (n : ℕ) := (Q n).mapIso (a F)
  refine ⟨fun F _ n ↦ (c F n).addCommGroupIsoToAddEquiv.trans
    (b (etaleTensorSectionsSheaf F) (hacyc F) n), ?_⟩
  intro F G _ _ φ n x
  have hn : (Q n).map
      ((SheafOfModules.toSheaf (moduleRings X.toRingedSpace)).map φ) ≫
        (c G n).hom = (c F n).hom ≫ (Q n).map (T.map (m F G φ)) := by
    change (Q n).map _ ≫ (Q n).map _ = (Q n).map _ ≫ (Q n).map _
    rw [← Functor.map_comp, ← Functor.map_comp, ha F G φ]
  have hx := congrArg (fun f ↦ f x) hn
  change (c G n).hom (((Q n).map
      ((SheafOfModules.toSheaf (moduleRings X.toRingedSpace)).map φ)) x) =
    ((Q n).map (T.map (m F G φ))) ((c F n).hom x) at hx
  change b (etaleTensorSectionsSheaf G) (hacyc G) n
      ((c G n).hom (((Q n).map
        ((SheafOfModules.toSheaf (moduleRings X.toRingedSpace)).map φ)) x)) = _
  exact (congrArg (b (etaleTensorSectionsSheaf G) (hacyc G) n) hx).trans
    (hb (etaleTensorSectionsSheaf F) (etaleTensorSectionsSheaf G)
      (hacyc F) (hacyc G) (m F G φ) n ((c F n).hom x))

end AlgebraicGeometry.Scheme.Modules
