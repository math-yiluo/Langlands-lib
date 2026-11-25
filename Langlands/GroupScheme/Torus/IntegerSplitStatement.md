# Statement: every torus over the integers is split

`Langlands.GroupScheme.IntegerTorusSplitStatement.{u}` states that every
`T : GroupScheme (Spec (CommRingCat.of (ULift.{u} ℤ)))` satisfying
`RelativeTorus.IsTorus T` also satisfies `IsSplitTorus T`. It is a
statement-only `Prop`-valued definition and supplies no proof or axiom.

`RelativeTorus.IsTorus` means that the actual group scheme becomes a finite
split torus on each member of an étale cover of its base. The rank may vary
between members in that definition. `IsSplitTorus T` means that there are a
finite type `I : Type u` and an isomorphism `T ≅ splitTorus (Spec ℤ) I`
over the entire base, where `splitTorus` is the categorical product of
copies of the actual multiplicative group scheme. Here `ℤ` in the base is
`ULift.{u} ℤ`, so no universe restriction is imposed.

The source is Brian Conrad, *Reductive group schemes* (2014), Corollary
B.3.6, p.293 (printed and one-based PDF page), registered as
`conrad-2014-reductive-group-schemes`, SHA-256
`1a63a17e4ccb7e23263d65f05d93a6651262861e978e9eb0c1c53a01fd59140a`.
After the general isotriviality theorem for groups of multiplicative type
over a normal irreducible scheme, Conrad explicitly deduces that all tori
over the integers are split, using the triviality of the étale fundamental
group of `Spec ℤ` (Minkowski). The paragraph before Proposition 6.4.1,
p.230, uses exactly this assertion for the maximal torus of a Chevalley
group. The étale-local convention agrees with Conrad's torus convention
by his Proposition B.3.4.

This statement is a prerequisite for
`ChevalleyGroupClassificationStatement`, and is more general than the
torus-splitting input needed there: it assumes neither an embedding into a
reductive group nor fibrewise maximality. It asserts only existence of a
global splitting, with no chosen coordinates or uniqueness claim.
