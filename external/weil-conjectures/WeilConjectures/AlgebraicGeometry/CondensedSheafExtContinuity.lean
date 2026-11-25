/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module
public import WeilConjectures.CategoryTheory.RingObjects.Condensed.FiniteSubextension
public import WeilConjectures.ConstructibleSheaf.ProEtaleModule.DerivedCategory
public import WeilConjectures.NumberTheory.Padics.FiniteCoefficientFields
import WeilConjectures.AlgebraicGeometry.CondensedConstructibleExtensionTower
import WeilConjectures.AlgebraicGeometry.CondensedLocalPieceHomContinuity

/-! # Filtered continuity for a constructible condensed module sheaf

Source: upstream ModuleObject/Colimit/TwoColimit.lean, module docstring, Sorried input (Hom);
Hemo--Richarz--Scholbach, Constructible sheaves, Lemma 5.3(2).
(auxiliary; not a blueprint node)

The comparison is `colimit.desc` of the cocone obtained by localization, shifting, and
additive Hom from `M[0]`. Thus its legs are postcomposition with the shifted colimit legs.
Naturality in the first argument and diagrams is built into additive coyoneda and the
colimit construction; compatibility with shifts uses the same construction for every integer.
-/

@[expose] public section

universe u

open CategoryTheory CategoryTheory.Limits Opposite

open scoped CategoryTheory.Obj

namespace AlgebraicGeometry.ProEtale

/-- Compose the functor mapping a cocone before specializing the ambient categories. -/
private theorem homColimitProperty_mapCocone_comp
    {A : Type*} [Category A] {B : Type*} [Category.{u + 1} B]
    [Preadditive B] [HasShift B ℤ]
    {I : Type (u + 1)} [SmallCategory I]
    (N : I ⥤ A) (c : Cocone N) (F : A ⥤ B) (K : B)
    (h : homColimitProperty (N ⋙ F) (F.mapCocone c) K) (n : ℤ) :
    IsIso (colimit.desc _
      ((F ⋙ shiftFunctor B n ⋙ preadditiveCoyoneda.obj (op K)).mapCocone c)) :=
  h n

noncomputable local instance localInst_CondensedSheafExtContinuity_1
    (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1})
    [MonObj Λ] (X : Scheme.{u}) :
    HasZeroMorphisms (Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1})
      (condensedRingObj Λ X)) := inferInstance

local instance localInst_CondensedSheafExtContinuity_2
    (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1})
    [MonObj Λ] (X : Scheme.{u}) {I : Type (u + 1)} [SmallCategory I]
    (N : I ⥤ CochainComplex (Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1})
      (condensedRingObj Λ X)) ℤ) : HasColimit N := by
  let C := Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1}) (condensedRingObj Λ X)
  have : HasColimitsOfShape I C := inferInstance
  have (n : ℤ) : HasColimit (N ⋙ HomologicalComplex.eval C (.up ℤ) n) :=
    HasColimitsOfShape.has_colimit _
  exact ⟨⟨⟨_, HomologicalComplex.isColimitCoconeOfHasColimitEval N⟩⟩⟩

/-- Derived Hom from a constructible condensed `E`-module sheaf commutes with a small
filtered colimit of complexes with a common termwise lower bound, in every integer shift.
Source: upstream ModuleObject/Colimit/TwoColimit.lean, Sorried input (Hom), sheaf base case;
Hemo--Richarz--Scholbach, Lemma 5.3(2).
(auxiliary; not a blueprint node)

Lean reduction: the open/closed one-step lemma gives a finite extension tower by
noetherian induction on closed supports. Continuity holds for the locally closed pieces
by the separate geometric lemma. Induction on the tower then uses the proved general
closure of Hom continuity under distinguished extensions. This is the comparison for
the original cocone, so no choice of a different colimit map is involved.

Expanded geometric argument (the named inputs below are DAG nodes):
1. By [lem-pur-ringed-site-grothendieck-abelian], filtered colimits of module sheaves are exact.
Thus for a strict filtered diagram the termwise colimit carries objectwise quasi-isomorphisms to
quasi-isomorphisms: its cohomology is the colimit of the kernels modulo the colimit of the images.
Consequently good truncation at a common cohomological lower bound does not change the comparison
being proved. Functorial K-injective resolutions exist by [prop-pur-kinjective-resolutions-exist];
replacing a strict diagram by these resolutions likewise leaves its termwise colimit
quasi-isomorphic to the original one. After computing a derived functor with these models, good
truncation at a common cohomological lower bound produces functorial bounded-below
representatives; those truncated representatives need not themselves be injective. We prove the
slightly more flexible assertion with a common cohomological lower bound, using such
representatives throughout; this includes the stipulated termwise bound. The underlying noetherian
space of $T$ is quasi-compact, and every open subset is quasi-compact, so intersections of affine
opens are quasi-compact and $T$ is quasi-separated. The same applies to its locally closed
subschemes.

2. The locally free case is valid on any quasi-compact quasi-separated scheme $V$. Suppose $P$ is
pro-etale locally free of finite rank. By [lem-weil-pbc-ringed-site-locally-free-derived-hom],
maps from $P[0]$ into $K[n]$ are $H^nR\Gamma(V,P^\vee\otimes K)$. Tensoring by $P^\vee$ preserves
the lower bound and commutes with the filtered colimit: on a trivializing cover it is a finite
direct sum, and the canonical tensor-colimit map is therefore an isomorphism locally, hence
globally. Apply the global-sections clause of [lem-weil-pbc-condensed-qcqs-pushforward-continuity]
to $P^\vee\otimes K_i$. This proves the desired comparison for $P$ for every integer $n$,
including negative $n$, and for arbitrary strict diagrams with a common cohomological lower bound.

3. For a closed immersion $i:Z\hookrightarrow V$ with complementary quasi-compact open immersion
$j$, use [lem-weil-pbc-condensed-open-closed-recollement] to write
$i_*Ri^!K\simeq\operatorname{Cone}(K\to Rj_*j^*K)[-1]$. The map here is the adjunction unit.
Pullback $j^*$ is exact and preserves sheaf colimits. By
[lem-weil-pbc-condensed-qcqs-pushforward-continuity] applied to the quasi-compact quasi-separated
$j$, the filtered-colimit comparison for $Rj_*j^*K_i$ is a quasi-isomorphism. In functorial
complex models, a cone has degree $r$ equal to the sum of the target's degree $r$ and the source's
degree $r+1$, with differential built from the unit. Termwise colimits therefore commute with this
cone and its differential; exact filtered colimits preserve the quasi-isomorphisms of models by
step 1. Applying $i^*$ and $i^*i_*\cong\mathrm{id}$ now identifies the colimit of the $Ri^!K_i$
with $Ri^!K$ by a quasi-isomorphism. The same recollement statement gives the common lower bound
$a$ for $Ri^!K_i$. Hence this new filtered diagram is an admissible second argument for the
inductive assertion; no constructibility hypothesis on it has been used.

4. Proceed by noetherian induction on closed subspaces $V$ of $T$, with the assertion quantified
over every constructible $E_V^c$-module $P$, every filtered diagram with a common cohomological
lower bound, and every integer shift. The empty scheme has the zero module category, so is the
base case. Let $(S_b)$ be a finite stratification as in [definition-constructible-sheaves--2]. For
each $b$, the boundary $F_b=\overline{S_b}\setminus S_b$ is closed in $V$ because $S_b$ is locally
closed. It has empty interior: a nonempty open contained in $F_b$ would be a nonempty relatively
open subset of $\overline{S_b}$ disjoint from its dense subset $S_b$. Set
$U=V\setminus\bigcup_bF_b$. This is dense open, since a finite intersection of dense open subsets
is dense (intersect a nonempty open with those dense opens one at a time). Each $S_b\cap
U=\overline{S_b}\cap U$ is closed in $U$, and its complement is the finite union of the other such
closed pieces, so it is also open. Apply [lem-weil-pbc-condensed-lfp-local-triviality] on the
noetherian strata and restrict its trivializations to these disjoint open pieces. Thus $P|_U$ is
locally free of finite rank. The closed complement $Z=V\setminus U$ is proper; intersecting the
strata with $Z$ gives a finite locally closed stratification and inverse image preserves their
presentations, since it preserves cokernels and finite free sheaves. Thus $i^*P$ is constructible
on $Z$. This uses no frontier condition on the partition and no induction on a potentially
unchanged count of strata. Exact restriction and its coefficient identifications are those of
[lem-weil-pbc-condensed-open-closed-recollement]. If a chosen stratum has a different scheme
structure from the corresponding open piece, its base change to that piece is a closed immersion
with full set-theoretic support. Apply the first recollement triangle with empty open complement:
restriction and closed pushforward are inverse, with the coefficient rings identified. Thus the
locally free restriction is the same one on the open piece; nilpotent scheme structures are not
silently identified.

5. Use the first triangle of [lem-weil-pbc-condensed-open-closed-recollement] for $P[0]$:
$j_!j^*P[0]\to P[0]\to i_*i^*P[0]\to$. For the first term the adjunction $j_!\dashv j^*$
identifies its shifted maps into $K_i$ with those from $j^*P[0]$ into $j^*K_i$; step 2 proves
their filtered continuity. For the third term $i_*\dashv Ri^!$ identifies the maps with those from
$i^*P[0]$ into $Ri^!K_i$. Step 3 identifies the colimit of the latter targets with $Ri^!K$ and
preserves a common lower bound. The noetherian induction hypothesis on the proper closed $Z$
therefore proves continuity for this third term for all shifts. The adjunction bijections identify
these comparison arrows with the arrows induced by the original cocone.

6. Apply [lem-weil-pbc-hom-out-of-triangle-exact] and its rotations to the triangle of step 5 with
targets $K_i[n]$ and $K[n]$. This gives the natural long exact Hom sequences in the first
argument. Take filtered colimits of the first sequences, which remain exact by
[lem-weil-pbc-filtered-colimit-abelian-groups-exact]. For each $n$, in the five-term window
the window with successive terms Hom(j_!j^*P,K_i[n-1]), Hom(i_*i^*P,K_i[n]),
Hom(P,K_i[n]), Hom(j_!j^*P,K_i[n]), and Hom(i_*i^*P,K_i[n+1]),
the four comparisons away from the middle are isomorphisms by step 5. The middle comparison is an
isomorphism by [lem-weil-pbc-five-lemma]. This completes the induction, and gives the claimed map
for $V=T$ and $P=M$.

7. The arrow proved invertible is the canonical comparison, defined on a representative $f:M[0]\to
N_i[n]$ by $f\mapsto (N_i[n]\to N[n])\circ f$. Precomposition with a map of first arguments and
postcomposition with a map of filtered diagrams commute with this rule by associativity of
composition. Replacing $n$ by $n+t$ gives exactly the shifted cocone rule, so shifts commute as
well. This proves all requested naturalities; it does not require making the chosen stratification
or noetherian induction functorial.
-/
theorem isIso_constructible_condensed_sheaf_hom_colimit
    (T : Scheme.{u}) [TopologicalSpace.NoetherianSpace T]
    (ℓ : ℕ) [Fact ℓ.Prime] (E : Padic.FiniteCoefficientFields ℓ (PadicAlgCl ℓ))
    (M : CategoryTheory.Mod (Sheaf (Scheme.ProEt.topology T) Ab.{u + 1})
      (condensedRingObj (Profinite.continuousMapRingObj E.val) T))
    (hM : IsConstructibleModuleObject (condensedRingObj (Profinite.continuousMapRingObj E.val) T) M)
    {I : Type (u + 1)} [SmallCategory I] [IsFiltered I]
    (N : I ⥤ CochainComplex
      (CategoryTheory.Mod (Sheaf (Scheme.ProEt.topology T) Ab.{u + 1})
        (condensedRingObj (Profinite.continuousMapRingObj E.val) T)) ℤ)
    (hN : ∃ a : ℤ, ∀ (i : I) (r : ℤ), r < a → IsZero ((N.obj i).X r))
    (n : ℤ) :
    IsIso (colimit.desc _
      ((DerivedCategory.Q ⋙ shiftFunctor _ n ⋙
        preadditiveCoyoneda.obj (op ((DerivedCategory.singleFunctor _ 0).obj M))).mapCocone
          (colimit.cocone N))) := by
  have hM' := exists_condensedConstructible_extension_tower T ℓ E M hM
  let D := N ⋙ DerivedCategory.Q
  let c := DerivedCategory.Q.mapCocone (colimit.cocone N)
  have hP : condensedConstructiblePiece T ℓ E ≤ homColimitProperty D c :=
    condensed_local_piece_hom_continuity T ℓ E N hN
  exact homColimitProperty_mapCocone_comp N (colimit.cocone N) DerivedCategory.Q _
    ((condensedConstructiblePiece T ℓ E).extensionProductIter_le_of_isTriangulatedClosed₂
      hP hM'.choose _ hM'.choose_spec) n

end AlgebraicGeometry.ProEtale
