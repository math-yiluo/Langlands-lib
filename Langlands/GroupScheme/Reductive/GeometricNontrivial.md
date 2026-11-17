# Nontrivial geometric fibres and arbitrary base change

Worker 632.

This internal helper packages the nontriviality assumption in the affine
adjoint and simply connected Weil-restriction statements. Its motivating
source is Brian Conrad, *Reductive group schemes* (2014), Proposition 6.4.4
and Remark 6.4.5, pp.232–233, registered as
`conrad-2014-reductive-group-schemes`. The source imposes nontrivial
geometric fibres to make the finite étale scheme of simple factors
surjective over the original base.

`HasNontrivialPoint G` means that on some scheme over the base, `G` has a
point different from the identity. It concerns the full represented functor
and does not require a nonidentity rational point. The proof first identifies
this condition with inequality of the top and bottom subgroup functors.
Fpqc reflection of a trivial subgroup functor then proves that fpqc
pullback preserves nontriviality. A nontrivial pullback reflects
nontriviality along any morphism, since one can forget the new base of its
test scheme. Nontriviality is also invariant under isomorphism.

Field extensions are fpqc, so they preserve and reflect this condition
without smoothness, affineness, finite type, algebraicity or separability
assumptions. Factoring a field-valued point through its residue-field
embedding gives the stated comparisons between arbitrary field-valued
pullbacks, actual residue-field fibres and the chosen geometric fibres.

`IsFibrewiseNontrivial G` requires `HasNontrivialPoint` for every chosen
geometric fibre. It is exactly the existential test-scheme condition in
the two motivating published statements. The composition isomorphism
for actual base changes and the field-valued comparison prove stability
under every base change; surjectivity of the base morphism suffices for
reflection. These results are internal consequences of the Library's
fpqc subgroup reflection and residue-fibre geometry. All schemes, fields
and test schemes lie in the arbitrary universe `u`.
