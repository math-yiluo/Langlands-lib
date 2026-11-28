# The smooth part of the compact-open completion

`Langlands.CompactCompletion.smoothCompletionEquiv` identifies a smooth
complex representation with the smooth part of its compact-open completion.
The group is a topological group whose compact open subgroups are cofinal
among open subgroups. The equivalence intertwines the group actions and is
natural under intertwiners, using the componentwise map of the completion.

This is the compact-open form of (I.1.5.2) in Renard,
*Représentations des groupes réductifs p-adiques*, French edition of 9 July
2026, printed p. 10 / PDF p. 16. VI.9.7 invokes the comparison in the
contragredient consequence on printed p. 206 / PDF p. 212. The registered
source is `renard-2026-representations-groupes-reductifs-padiques`, SHA-256
`7b539996793b7c3620e72e1e389588eb42d1a8e91d6f68b2eead5c2e2ffc182c`.

The equivalence sends \(v\) to the family of averages \(e_Kv\). Averaging
over a larger subgroup absorbs averaging over a smaller one, which gives
compatibility. Conjugation of the averaging subgroups gives equivariance,
and evaluation at a subgroup fixing the difference of two vectors gives
injectivity. If a family \(x\) is fixed by a compact open subgroup \(K\),
then for every index \(L\) there is an index below \(K\cap L\) whose
component is \(K\)-fixed. Averaging that component to \(K\) leaves it
unchanged, so it equals \(x_K\). Averaging to \(L\) then shows
\(e_Lx_K=x_L\). Every smooth family admits such a \(K\), and evaluation at
any such \(K\) gives the inverse. Compact averaging commutes with
intertwiners, giving the naturality formula.
