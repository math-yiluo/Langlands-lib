module

public import Mathlib.Algebra.Category.Grp.Abelian
public import Mathlib.Algebra.Category.Grp.EpiMono
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.Abelian
public import Mathlib.CategoryTheory.Abelian.RightDerived
public import Mathlib.CategoryTheory.Limits.Shapes.Countable
public import Mathlib.CategoryTheory.Sites.Abelian
public import Mathlib.CategoryTheory.Sites.EpiMono
public import Mathlib.CategoryTheory.Sites.Spaces
public import Mathlib.Combinatorics.Quiver.ReflQuiver
public import Mathlib.Order.CompletePartialOrder
import Mathlib.Tactic.CrossRefAttribute

set_option autoImplicit false
set_option maxSynthPendingDepth 3

@[expose] public section

set_option backward.isDefEq.respectTransparency false

/-!
# Locality of cohomology

A cohomology class of positive degree on a sheaf of `O_X`-modules vanishes after restriction to
the members of a suitable open covering.

Throughout, `X` is a ringed space, i.e. a topological space equipped with a sheaf of
commutative unital rings `O_X`, and `Mod(O_X)` denotes the abelian category of sheaves of
`O_X`-modules, which has enough injectives.

## Main definitions

* `secF R U`: the global-sections-over-`U` functor `Mod(O_X) ⥤ AddCommGrpCat`.
* `Hgroup R U n F`: the cohomology `Hⁿ(U, F)`, obtained by choosing an injective resolution
  `0 → F → I^•` in `Mod(O_X)` and taking `Hⁿ(Γ(U, I^•))`; equivalently the `n`-th right derived
  functor of `secF R U` applied to `F`.  This is independent of the resolution up to canonical
  isomorphism.
* `Hrestrict R h n F`: for `U ≤ V`, the restriction map `Hⁿ(V, F) → Hⁿ(U, F)` induced by the
  restriction maps of the resolution, functorial in `F` and independent of the resolution.

## Main results

* `locality_of_cohomology`: for `n > 0` and `ξ ∈ Hⁿ(U, F)` there is an open covering
  `U = ⨆ i, Uᵢ` with `ξ|_{Uᵢ} = 0` in `Hⁿ(Uᵢ, F)` for every `i`.

## Implementation notes

- A "ringed space" is encoded directly by its structure sheaf, a `RingCat`-valued sheaf
  `R : Sheaf (Opens.grothendieckTopology X) RingCat` on the topological space `X`. This is exactly
  the data consumed by Mathlib's `SheafOfModules R`, the abelian category
  $\mathit{Mod}(\mathcal{O}_X)$.
- `H^n(U, \mathcal{F})` is realized as the $n$-th right derived functor (`Functor.rightDerived`) of
  the global-sections-over-$U$ functor `secF R U : SheafOfModules R ⥤ AddCommGrpCat`, which is
  `SheafOfModules.toSheaf R` (forget to abelian-group sheaves) followed by evaluation at `U`. This
  computes cohomology via injective resolutions, matching Definition 1, since right derived
  functors are defined through injective resolutions and are independent of the chosen resolution.
- The restriction map (Definition 2) is obtained functorially: `sheafSections` is a functor in the
  open `U`, so `U ≤ V` induces a natural transformation `secF R V ⟶ secF R U`, and
  `NatTrans.rightDerived` transports it to `H^n(V, F) ⟶ H^n(U, F)`.
- We assume the standard hypotheses making `SheafOfModules R` an abelian category with enough
  injectives (`HasSheafify`, `WEqualsLocallyBijective`, `EnoughInjectives`), reflecting the fact
  that `Mod(O_X)` has enough injectives.

## References

* [Stacks Project, Tag 01E3](https://stacks.math.columbia.edu/tag/01E3)
-/

open CategoryTheory Opposite TopologicalSpace

universe u

variable {X : Type u} [TopologicalSpace X]
-- The structure sheaf `O_X` of the ringed space, encoded as a `RingCat`-valued sheaf.
variable (R : Sheaf (Opens.grothendieckTopology X) RingCat)
-- Standard hypotheses ensuring `Mod(O_X) = SheafOfModules R` is abelian with enough injectives.
variable [HasSheafify (Opens.grothendieckTopology X) AddCommGrpCat]
variable [(Opens.grothendieckTopology X).WEqualsLocallyBijective AddCommGrpCat]
variable [EnoughInjectives (SheafOfModules R)]

-- Main Definition(s)

-- Auxiliary lemmas for the proof of Tag 01E3

/- **`toSheaf` of an injective resolution is exact in positive degree (as sheaves of abelian
groups).**
The forgetful functor `SheafOfModules.toSheaf R : Mod(O_X) ⥤ Sheaf(Ab)` is exact (it is the
composite
of forgetting module structure and the inclusion into presheaves, reflecting/forgetting along exact
functors; in particular it preserves exactness of short complexes). An injective resolution `I` of
`F`
has `I.cocomplex` exact at every degree `k + 1` (`InjectiveResolution.cocomplex_exactAt_succ`).
Applying
the exact functor `toSheaf R` degreewise preserves this exactness, so the complex of sheaves of
abelian
groups `(toSheaf R).mapHomologicalComplex |>.obj I.cocomplex` is exact at degree `k + 1`.
-/

/-- **Diagram-shifting transfer for colimit preservation.**
If `G` preserves the colimit of `E` and `G ⋙ F` preserves the colimit of `E`, then `F` preserves
the colimit of `E ⋙ G`. (The colimit cocone of `E ⋙ G` is `G.mapCocone (colimit.cocone E)`, a
colimit since `G` preserves it; `F` maps it to `(G ⋙ F).mapCocone (colimit.cocone E)`, a colimit
since `G ⋙ F` preserves it.) -/
theorem preservesColim_comp_transfer {A B Dc : Type _} [Category A] [Category B] [Category Dc]
    {K : Type _} [Category K] (E : K ⥤ A) (G : A ⥤ B) (F : B ⥤ Dc)
    (hG : Limits.PreservesColimit E G) (hGF : Limits.PreservesColimit E (G ⋙ F))
    (hE : Limits.HasColimit E) :
    Limits.PreservesColimit (E ⋙ G) F :=
  Limits.preservesColimit_of_preserves_colimit_cocone
    (Limits.isColimitOfPreserves G (Limits.colimit.isColimit E))
    (Limits.isColimitOfPreserves (G ⋙ F) (Limits.colimit.isColimit E))

/-- **`SheafOfModules.toSheaf R` preserves finite colimits.**
Both `SheafOfModules R` and `Sheaf J Ab` compute colimits by sheafifying the underlying presheaf
colimit, and `toSheaf` commutes with this. Concretely, write
`Lsh = PresheafOfModules.sheafification` (a left adjoint, hence preserves all colimits) and
`Gsh = forget R ⋙ restrictScalars`. The counit of `PresheafOfModules.sheafificationAdjunction` is
an isomorphism, so `Gsh ⋙ Lsh ≅ 𝟭`. Moreover
`Lsh ⋙ toSheaf R ≅ toPresheaf R.obj ⋙ presheafToSheaf J Ab` (`sheafificationCompToSheaf`), and the
right-hand composite preserves finite colimits because `toPresheaf` does and `presheafToSheaf` does
(as the left adjoint of `sheafificationAdjunction`). Given a finite diagram `D`, the transfer lemma
applied to `E := D ⋙ Gsh`, `G := Lsh`, `F := toSheaf R` shows `toSheaf R` preserves the colimit of
`(D ⋙ Gsh) ⋙ Lsh ≅ D`. -/
noncomputable instance toSheafPFC : Limits.PreservesFiniteColimits (SheafOfModules.toSheaf R) := by
  refine ⟨fun K _ _ => ?_⟩
  set Lsh : PresheafOfModules R.obj ⥤ SheafOfModules R :=
    PresheafOfModules.sheafification (𝟙 R.obj)
  set Gsh : SheafOfModules R ⥤ PresheafOfModules R.obj :=
    SheafOfModules.forget R ⋙ PresheafOfModules.restrictScalars (𝟙 R.obj)
  -- `Lsh` preserves colimits of shape `K` (it is a left adjoint).
  have lshPres : Limits.PreservesColimitsOfShape K Lsh :=
    ((PresheafOfModules.sheafificationAdjunction
      (𝟙 R.obj)).leftAdjoint_preservesColimits).preservesColimitsOfShape
  -- `Lsh ⋙ toSheaf R` preserves colimits of shape `K`, built from clean pieces.
  have compPres : Limits.PreservesColimitsOfShape K (Lsh ⋙ SheafOfModules.toSheaf R) := by
    have hiso : Lsh ⋙ SheafOfModules.toSheaf R ≅
        PresheafOfModules.toPresheaf R.obj ⋙
          presheafToSheaf (Opens.grothendieckTopology X) AddCommGrpCat :=
      PresheafOfModules.sheafificationCompToSheaf (𝟙 R.obj)
    have hcleanToP : Limits.PreservesColimitsOfShape K (PresheafOfModules.toPresheaf R.obj) :=
      (inferInstance : Limits.PreservesFiniteColimits
        (PresheafOfModules.toPresheaf R.obj)).preservesFiniteColimits K
    have hcleanPTS : Limits.PreservesColimitsOfShape K
        (presheafToSheaf (Opens.grothendieckTopology X) AddCommGrpCat) :=
      ((sheafificationAdjunction (Opens.grothendieckTopology X)
        AddCommGrpCat).leftAdjoint_preservesColimits).preservesColimitsOfShape
    have hcomp : Limits.PreservesColimitsOfShape K
        (PresheafOfModules.toPresheaf R.obj ⋙
          presheafToSheaf (Opens.grothendieckTopology X) AddCommGrpCat) :=
      Limits.comp_preservesColimitsOfShape _ _
    exact Limits.preservesColimitsOfShape_of_natIso hiso.symm
  -- The counit of the sheafification adjunction is an isomorphism: `Gsh ⋙ Lsh ≅ 𝟭`.
  have counitIso : Gsh ⋙ Lsh ≅ 𝟭 (SheafOfModules R) :=
    asIso (PresheafOfModules.sheafificationAdjunction (𝟙 R.obj)).counit
  refine ⟨fun {D} => ?_⟩
  have key : Limits.PreservesColimit ((D ⋙ Gsh) ⋙ Lsh) (SheafOfModules.toSheaf R) :=
    preservesColim_comp_transfer (D ⋙ Gsh) Lsh (SheafOfModules.toSheaf R)
      (lshPres.preservesColimit) (compPres.preservesColimit) inferInstance
  have hdiso : (D ⋙ Gsh) ⋙ Lsh ≅ D :=
    (Functor.associator D Gsh Lsh) ≪≫ Functor.isoWhiskerLeft D counitIso ≪≫ D.rightUnitor
  exact Limits.preservesColimit_of_iso_diagram (SheafOfModules.toSheaf R) hdiso

-- Main Statement(s)
