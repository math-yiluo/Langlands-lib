# Zariski gluing of rigidified abelian-scheme classes

`Langlands.AbelianScheme.RigidifiedClassesZariskiGluingStatement.{u}` states
the gluing half of the Zariski sheaf property for actual rigidified
isomorphism classes on an abelian scheme. It defines a proposition only;
the proof is a separate obligation.

## Exact interface

For every scheme `S : Scheme.{u}`, abelian scheme `A : AbelianScheme S`,
test `T : Over S` and open cover `𝒰 : T.left.OpenCover.{u}`, let `q i` be
an actual rigidified class over the member
`Over.mk (𝒰.f i ≫ T.hom)`. Suppose the pullbacks of `q i` and `q j` to
every pairwise overlap `pullback (𝒰.f i) (𝒰.f j)` agree. Then there exists
`q₀ : RigidifiedClasses A T` whose pullback to every member is `q i`.

The overlap is viewed as an `S`-scheme through its first projection:

```lean
Over.mk (pullback.fst (𝒰.f i) (𝒰.f j) ≫ 𝒰.f i ≫ T.hom)
```

Its maps to members `i` and `j` are the actual slice morphisms induced by
`pullback.fst` and `pullback.snd`. The second is well defined because
`pullback.condition_assoc` identifies the two composites to `S`.
Both sides of the overlap equality therefore belong to the same published
class type.

`RigidifiedClasses A T` is the published quotient of the category
`RigidifiedFamily A T` by rigidified isomorphism. A representative is an
actual line bundle on the chosen total space `T ×_S A`, with a
rigidification along `(id_T, unitSection A ∘ T.hom)`. The maps in the
statement are the published `RigidifiedLineBundle.classesPullback`,
defined by `Quotient.map` from the actual relative rigidified pullback
functor. No substitute quotient or abstract class functor is introduced.

The cover index universe is explicitly `u`; leaving it implicit would
leave an unsolved universe metavariable in this definition. The base and
test schemes are arbitrary, including nonreduced and non-quasi-separated
schemes. The cover may be infinite and its members need not be affine.
No quasi-separatedness, affineness, finiteness, representability,
universal-family, class-sheaf, automorphism-rigidity, global-functions
or cocycle hypothesis is added.

The conclusion asserts existence of a global class. The published
`RigidifiedClassesZariskiSeparatedStatement` is the separate uniqueness
half. Together their assertions express the Zariski sheaf property for
the published rigidified classes and pullbacks.

## Derived provenance and purpose

This is a derived, Zariski-only consequence of the fppf sheaf property in
Edixhoven, van der Geer and Moonen, *Abelian Varieties*, preliminary draft,
Chapter VI §1, (6.2)(iii), printed pp.88–89 / PDF pp.92–93. The registered
source is `edixhoven-vandergeer-moonen-abelian-varieties-draft`, SHA-256
`81e88e484e1e830286ffed93d4636c80e50a1c341ffe19cc198bd856be713b42`,
retained as
`literature/Edixhoven, van der Geer, Moonen - Abelian Varieties (preliminary version of the first chapters).pdf`.
These pages were read directly. No source-specific note was present at
`notes/errata/edixhoven-vandergeer-moonen-abelian-varieties-draft.md`
in the workspace, project notes or published Library when checked.

Under hypotheses `(∗)`, the source assumes that `f : X → S` is
quasi-compact and quasi-separated, has a section, and satisfies
`f_* O_(X ×_S T) = O_T` for every `S`-scheme `T`. It defines rigidified
line bundles and their isomorphism classes, explains the absence of
nontrivial rigidified automorphisms, and states in (iii) that the
rigidified class functor is an fppf sheaf by descent theory for line
bundles. The present proposition specializes to abelian schemes and to
Zariski gluing. It does not state the full fppf result or an ordinary
Picard comparison. The Library uses `T ×_S A` in place of the source's
`A ×_S T`; its published relative geometry accounts for the symmetry.

An abelian scheme's structure morphism is proper, hence quasi-compact
and quasi-separated, regardless of whether `S` or `T` is
quasi-separated. Its unit supplies the section. The applicable
global-functions result is already published as
`Langlands.AbelianScheme.universalGlobalFunctions`; the source's
global-functions hypothesis is therefore an obligation discharged
inside the proof, rather than an extra hypothesis of this statement.

This gluing interface is needed for Zariski-local construction of
universal rigidified families. Local universal families determine
compatible classes on a glued parameter, and the conclusion supplies a
class represented by an actual global rigidified family. The interface
is deliberately parallel to the published separatedness statement.
It asserts no representability or universality theorem itself.

## Remaining proof obligations

Choose representatives of the local classes. Equality of their classes
on each overlap supplies only some rigidified isomorphism there.
These witnesses do not come with a cocycle condition. After transporting
iterated pullbacks by the published pullback coherence, the published
`Langlands.AbelianScheme.rigidifiedIsoUniqueness` can discharge that
condition: the two rigidified isomorphisms in each cocycle equation
have the same source and target, hence are equal.

A proof must then construct an actual glued line bundle on `T ×_S A`,
by object gluing of sheaves of modules over its pulled-back open cover,
and check that the glued sheaf is locally free of rank one. The
published module morphism and isomorphism gluing results glue maps
between supplied objects; they do not alone construct this object.
One must also glue its rigidification, verify the local rigidified
identifications and pass to the actual quotient class `q₀`.
This construction must retain all the schemes and covers quantified
above. These are obligations of the separate exact-target proof task.
